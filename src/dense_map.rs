use std::{cmp::Ordering, vec};

use byteorder::{ByteOrder, NativeEndian, WriteBytesExt};

const ITEMS_PER_PAGE: u16 = 1024;

pub struct DenseMap {
    key_len: usize,
    value_len: usize,
    len: usize,
    levels: Vec<Level>,
    tmp_buffer: Vec<u8>,
}

impl DenseMap {
    pub fn new(key_len: usize, value_len: usize) -> Self {
        assert!(key_len > 0);

        Self {
            key_len,
            value_len,
            len: 0,
            levels: vec![],
            tmp_buffer: vec![],
        }
    }

    pub fn len(&self) -> usize {
        self.len
    }

    pub fn get(&self, key: &[u8]) -> Option<&[u8]> {
        assert_eq!(key.len(), self.key_len);

        for level in self.levels.iter() {
            if let Some(result) = level.get(key) {
                return Some(result);
            }
        }

        None
    }

    pub fn get_mut_or_insert(&mut self, key: &[u8], default_value: &[u8]) -> &mut [u8] {
        assert_eq!(key.len(), self.key_len);
        assert_eq!(default_value.len(), self.value_len);

        for level in self.levels.iter_mut() {
            if let Some(result) = level.get_mut_ptr(key) {
                return unsafe { &mut *result };
            }
        }

        'outer: while let Some(level_a) = self.levels.pop() {
            if let Some(level_b) = self.levels.pop() {
                if level_b.len() <= level_a.len() {
                    self.levels.push(Level::merge(level_a, level_b));
                } else {
                    self.levels.push(level_b);
                    self.levels.push(level_a);
                    break 'outer;
                }
            } else {
                self.levels.push(level_a);
                break;
            }
        }

        self.tmp_buffer.clear();
        self.tmp_buffer.extend_from_slice(key);
        self.tmp_buffer.extend_from_slice(default_value);

        self.levels.push(Level::singleton(&self.tmp_buffer));
        self.len += 1;

        &mut self.levels.last_mut().unwrap().root[2 + key.len()..]
    }
}

struct Level {
    entry_len: usize,
    len: usize,
    pages: Box<[Box<[u8]>]>,
    root: Box<[u8]>,
}

impl Level {
    pub fn singleton(data: &[u8]) -> Self {
        let page = Box::new([]) as Box<[u8]>;
        let pages = Box::new([page]);

        let mut root = Vec::with_capacity(data.len() + 2);
        root.write_u16::<NativeEndian>(0).unwrap();
        root.extend_from_slice(data);

        Level {
            entry_len: data.len(),
            len: 1,
            pages,
            root: root.into_boxed_slice(),
        }
    }

    pub fn merge(a: Level, b: Level) -> Self {
        let len = a.len() + b.len();
        let pages_count = (len + ITEMS_PER_PAGE as usize - 1) / ITEMS_PER_PAGE as usize;

        assert_eq!(a.entry_len, b.entry_len);
        let entry_len = a.entry_len;

        let mut stream_a = a.into_stream();
        let mut stream_b = b.into_stream();

        let mut new_page = true;
        let mut page = Vec::with_capacity(entry_len * ITEMS_PER_PAGE as usize);
        let mut page_len = 0;
        let mut pages = Vec::with_capacity(pages_count);
        let mut root = Vec::with_capacity(pages_count * (ITEMS_PER_PAGE as usize + 2));
        let mut last_page_root_offset = 0;

        let mut stream_a_next = stream_a.next();
        let mut stream_b_next = stream_b.next();

        macro_rules! add_item {
            ($item:expr) => {{
                let item = $item;
                if new_page {
                    root.write_u16::<NativeEndian>(0).unwrap();
                    root.extend_from_slice(item);
                    new_page = false;
                } else {
                    page.extend_from_slice(item);
                    page_len += 1;
                }
            }};
        }

        let mut done = false;

        while !done {
            match stream_a_next.cmp(&stream_b_next) {
                Ordering::Less => {
                    add_item!(stream_b_next.unwrap());
                    stream_b_next = stream_b.next();
                }
                Ordering::Greater => {
                    add_item!(stream_a_next.unwrap());
                    stream_a_next = stream_a.next();
                }
                Ordering::Equal => unreachable!(),
            }

            done = stream_a_next.is_none() && stream_b_next.is_none();

            if done || page_len == ITEMS_PER_PAGE {
                NativeEndian::write_u16(
                    &mut root[last_page_root_offset..last_page_root_offset + 2],
                    page_len,
                );
                pages.push(page.into_boxed_slice());
                new_page = true;
                page = Vec::with_capacity(entry_len * ITEMS_PER_PAGE as usize);
                page_len = 0;
                last_page_root_offset = root.len();
            }
        }

        Level {
            entry_len,
            len,
            pages: pages.into_boxed_slice(),
            root: root.into_boxed_slice(),
        }
    }

    pub fn len(&self) -> usize {
        self.len
    }

    fn into_stream(self) -> LevelIntoStream {
        LevelIntoStream {
            entry_len: self.entry_len,
            pages: Vec::from(self.pages).into_iter(),
            current_page: Box::new([]),
            root: self.root,
            root_index: 0,
            page_index: 0,
            page_len: 0,
        }
    }

    pub fn get<'a>(&'a self, key: &[u8]) -> Option<&'a [u8]> {
        let mut low = 0;
        let mut high = self.pages.len();

        while low < high {
            let mid = low + (high - low) / 2;

            let view_len = self.entry_len + 2;
            let view_offset = mid * view_len;

            let root_view = &self.root[view_offset..view_offset + view_len];

            let root_key = &root_view[2..2 + key.len()];

            match root_key.cmp(key) {
                Ordering::Less => {
                    high = mid;
                }
                Ordering::Greater => {
                    low = mid + 1;
                }
                Ordering::Equal => {
                    return Some(&root_view[2 + key.len()..]);
                }
            }
        }

        if low == 0 {
            return None;
        }

        let page_index = low - 1;

        let view_len = self.entry_len + 2;
        let view_offset = page_index * view_len;

        let page_len = NativeEndian::read_u16(&self.root[view_offset..view_offset + 2]) as usize;

        let page = &self.pages[page_index];

        let mut low = 0;
        let mut high = page_len;

        while low < high {
            let mid = low + (high - low) / 2;

            let data_offset = mid * self.entry_len;

            let data = &page[data_offset..data_offset + self.entry_len];

            let data_key = &data[..key.len()];

            match data_key.cmp(key) {
                Ordering::Less => {
                    high = mid;
                }
                Ordering::Greater => {
                    low = mid + 1;
                }
                Ordering::Equal => {
                    return Some(&data[key.len()..]);
                }
            }
        }

        None
    }

    fn get_mut_ptr(&mut self, key: &[u8]) -> Option<*mut [u8]> {
        let mut low = 0;
        let mut high = self.pages.len();

        while low < high {
            let mid = low + (high - low) / 2;

            let view_len = self.entry_len + 2;
            let view_offset = mid * view_len;

            let root_view = &mut self.root[view_offset..view_offset + view_len];

            let root_key = &root_view[2..2 + key.len()];

            match root_key.cmp(key) {
                Ordering::Less => {
                    high = mid;
                }
                Ordering::Greater => {
                    low = mid + 1;
                }
                Ordering::Equal => {
                    return Some(&mut root_view[2 + key.len()..] as *mut _);
                }
            }
        }

        if low == 0 {
            return None;
        }

        let page_index = low - 1;

        let view_len = self.entry_len + 2;
        let view_offset = page_index * view_len;

        let page_len = NativeEndian::read_u16(&self.root[view_offset..view_offset + 2]) as usize;

        let page = &mut self.pages[page_index];

        let mut low = 0;
        let mut high = page_len;

        while low < high {
            let mid = low + (high - low) / 2;

            let data_offset = mid * self.entry_len;

            let data = &mut page[data_offset..data_offset + self.entry_len];

            let data_key = &data[..key.len()];

            match data_key.cmp(key) {
                Ordering::Less => {
                    high = mid;
                }
                Ordering::Greater => {
                    low = mid + 1;
                }
                Ordering::Equal => {
                    return Some(&mut data[key.len()..] as *mut _);
                }
            }
        }

        None
    }
}

struct LevelIntoStream {
    entry_len: usize,
    pages: vec::IntoIter<Box<[u8]>>,
    current_page: Box<[u8]>,
    root: Box<[u8]>,
    root_index: usize,
    page_index: usize,
    page_len: usize,
}

impl LevelIntoStream {
    pub fn next(&mut self) -> Option<&[u8]> {
        if self.page_index == self.page_len {
            self.current_page = self.pages.next()?;

            let view_len = self.entry_len + 2;
            let view_offset = self.root_index * view_len;
            self.root_index += 1;

            let root_view = &self.root[view_offset..view_offset + view_len];

            let root_data = &root_view[2..];
            self.page_len = NativeEndian::read_u16(&root_view[..2]) as usize;
            self.page_index = 0;

            Some(root_data)
        } else {
            let data_offset = self.page_index * self.entry_len;
            self.page_index += 1;

            let page_data = &self.current_page[data_offset..data_offset + self.entry_len];

            Some(page_data)
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;

    use proptest::prelude::*;
    use rustc_hash::FxHashMap as HashMap;

    #[test]
    fn many_byte_inserts() {
        crate::logging::setup(false);

        proptest!(|(inserts in prop::collection::vec(any::<[u8; 2]>(), 10..10000))| {
            let mut dense_map = DenseMap::new(1, 1);
            let mut ref_map = HashMap::default();
            for data in inserts.iter() {
                ref_map.insert(data[0], data[1]);
                dense_map.get_mut_or_insert(&data[0..1], &data[1..2]).copy_from_slice(&data[1..2]);
            }

            for (&key, &value) in ref_map.iter() {
                prop_assert_eq!(dense_map.get(&[key]).unwrap(), &[value]);
            }

            for byte in 0..=255u8 {
                if !ref_map.contains_key(&byte) {
                    prop_assert!(dense_map.get(&[byte]).is_none());
                }
            }
        });
    }

    #[test]
    fn many_two_byte_inserts() {
        crate::logging::setup(false);

        proptest!(|(inserts in prop::collection::vec(any::<[u8; 3]>(), 10..10000))| {
            let mut dense_map = DenseMap::new(2, 1);
            let mut ref_map = HashMap::default();
            for data in inserts.iter() {
                ref_map.insert([data[0], data[1]], data[2]);
                dense_map.get_mut_or_insert(&data[0..2], &data[2..3]).copy_from_slice(&data[2..3]);
            }

            for (&key, &value) in ref_map.iter() {
                prop_assert_eq!(dense_map.get(&key).unwrap(), &[value]);
            }
        });
    }
}
