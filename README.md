# Lower Size Bounds for Sorting Networks

This is an implementation of a new search procedure for finding lower bounds
for the size of sorting networks. Using this search procedure I was able to
show that sorting 11 inputs requires 35 comparisons, improving upon the
previously best known lower bound of 33 comparisons. This in turn improves the
lower bound for 12 inputs to 39 comparisons. As sorting networks matching these
bounds are already known, both new lower bounds are tight.

This repository contains the following components:

  * A log generating search procedure, implemented in Rust.
  * Pruning and post-processing of search logs, implemented in Rust.
  * A formally verified checker for the certificates generated from search
    logs, implemented using Haskell and Isabelle/HOL.

I'm currently working on a document explaining the methods used. I will add a
draft to this repository as soon as it is ready. You can also [follow me on
twitter][twitter] for updates about this.

## Usage

To perform the search and verify the result, use:

```
bash search_and_verify.sh CHANNELS DATADIR
```

If you have a proof certificate generated from the search logs, it can be
checked using:

```
bash verify_proof_cert.sh CERTBIN
```

## System Requirements

To compile the search procedure, a recent Rust compiler and the Rust package
manager Cargo (e.g. as installed via [rustup]) are
required.

The formally verified checker uses the ["Haskell Tool Stack"][stack].

Checking the formal proof of the verified checker and re-exporting the verified
Haskell code requires [Isabelle2019][isabelle].

Performing the search for 9 input channels (replicating the previously best
known result) requires very little resources and is a good way to make sure
that a system is set up correctly. The first time `bash search_and_verify.sh 9
data` is run, it will compile the required Rust and Haskell code. Subsequent
runs will use cached binaries. For 9 input channels the search and verification
require less than 50MB of ram and finishes within 10 seconds on my laptop.

Performing the search and certificate generation for 11 input channels requires
a bit below 200GB of ram and took below 80 hours on an AMD "EPYC 7401P" 24-core
(48-thread) processor. Available threads will be used automatically.
Distribution across multiple machines is not supported.

Checking the resulting certificate for 11 input channels is less demanding. It
takes below 8GB and around 3 hours on my laptop.

## Certificates

A 1.2GB compressed certificate for 11 input channels is available for download:
[proof_cert_11.bin.zst][cert11]. It is compressed using [Zstandard][zst] and
needs to be unpacked before it can be checked. The SHA-256 hash of the
uncompressed certificate is
`7fe9f5cd694714bf83da0bcab162a290eb076ad4257265507a74cea8fab85b7e`

## Formal Verification

The certificate checker consists of an unverified part that parses the
certificate and a formally verified part that checks the parsed data. The
formally verified part is extracted from a specification and proof written
using Isabelle/HOL. This part is contained in the subdirectory
`checker/verified`.

A small patch, `strict_and_parallel.patch`, is applied to the extracted code. It
is easy to manually verify that this patch only affects the evaluation order,
not the result of running the extracted program. This is done to speed up the
checking and to allow the use of multiple threads. Given enough time it is
possible to run the checking without this patch.

A current snapshot of the extracted code is part of the repository. This allows
running the checker without requiring Isabelle. To update and reverify the
extracted code run `checker/update_extracted_code.sh`.

Currently the formal proof is without comments and not intended for humans to
read. An exception to this is the definition of sorting networks and lower size
bounds for sorting networks as well as the final lemma
`check_proof_get_bound_spec` showing the correctness of the checker. These are
contained in `Sorting_Network_Bound.thy` and `Checker_Codegen.thy`
respectively.

As Isabelle/HOL code uses escape sequences for various non-ASCII symbols, it is
best viewed using Isabelle/jEdit. Alternatively a [current snapshot of the
formal proof is available in PDF form][document.pdf].

[rustup]: https://rustup.rs/
[stack]: https:/haskellstack.org
[isabelle]: https://isabelle.in.tum.de/
[cert11]: https://files.jix.one/sortnetopt/proof_cert_11.bin.zst
[zst]: https://facebook.github.io/zstd/
[document.pdf]: https://files.jix.one/sortnetopt/document.pdf
[twitter]: https://twitter.com/jix_
