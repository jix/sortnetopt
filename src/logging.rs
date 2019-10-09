use std::io::Write;

pub fn setup(print_mem_usage: bool) {
    better_panic::install();
    let startup = std::time::Instant::now();

    let _ = env_logger::Builder::from_env(env_logger::Env::default().default_filter_or("info"))
        .format(move |buf, record| {
            let elapsed = startup.elapsed().as_millis();
            let minutes = elapsed / 60000;
            let seconds = (elapsed % 60000) / 1000;
            let millis = elapsed % 1000;

            if print_mem_usage {
                let (mem, unit) = get_mem_usage();
                writeln!(
                    buf,
                    "{:3}:{:02}.{:03} [{:4} {}]: {}",
                    minutes,
                    seconds,
                    millis,
                    mem,
                    unit,
                    record.args()
                )
            } else {
                writeln!(
                    buf,
                    "{:3}:{:02}.{:03}: {}",
                    minutes,
                    seconds,
                    millis,
                    record.args()
                )
            }
        })
        .is_test(cfg!(test))
        .try_init();
}

fn get_mem_usage() -> (usize, &'static str) {
    let prefix = "VmHWM:";
    if let Some(mem_line) = std::fs::read_to_string("/proc/self/status")
        .unwrap()
        .lines()
        .filter(|line| line.starts_with(prefix))
        .next()
    {
        let usage_kb_str = mem_line[prefix.len()..].trim();
        let usage_kb = str::parse::<usize>(&usage_kb_str[..usage_kb_str.len() - 3]).unwrap();

        if usage_kb > 10 * 1024 * 1024 {
            return (usage_kb / (1024 * 1024), "G");
        } else if usage_kb > 10 * 1024 {
            return (usage_kb / 1024, "M");
        } else {
            return (usage_kb, "k");
        }
    }

    (0, "?")
}
