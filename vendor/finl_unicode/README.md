# finl Unicode support

This crate is designed for the Unicode needs of the finl project, but is designed to be usable by other software as well.
In the current release (1.0.x), support is provided for character code identification and grapheme segmentation and Unicode14.0.0.

## Overview 

### Category identification

Loading the `finl_unicode` crate with the `categories` feature will add methods onto the char type to test the category of a character
or identify its category. See the rustdoc for detail.

### Grapheme clusters

Loading the `finl_unicode` crate with the `grapheme_clusters` feature will extend `Peekable<CharIndices>` to have a `next_cluster()` method which will return the next grapheme cluster from the iterator.
There is also a pure cluster iterator available by calling `Graphemes::new(s)` on a `&str`. I don’t use this in finl, but wrote it using the same algorithm as the extension of `Peekable<CharIndices>` for the purposes of benchmarking.¹

## Why?

There *are* existing crates for these purposes, but segmentation lacked the interface for segmentation that I wanted (which was to be able to extend `Peekable<CharIndices>` with a method to fetch the next grapheme cluster if it existed). 
I incorrectly assumed that this would require character code identification, which turned out to be incorrect, but it turned out that the crate I was using was outdated and possibly abandoned and had an inefficient algorithm so it turned out to be a good thing that I wrote it.
I did benchmarks comparing my code against existing crates and discovered that I had managed to eke out performance gains against all of them, so that’s an added bonus.

###  Benchmark results

All benchmarks are generated using Criterion You can replicate them by running `cargo bench` from the project directory. Three numbers are given for all results: low/mean/high, all from the output of Criterion. The mean value is given in **bold**. 

#### Unicode categories
I ran three benchmarks to compare the performance of the crates on my M3 Max MacBook Pro. 
The Japanese text benchmark reads the Project Gutenberg EBook of *Kumogata monsho* by John Falkner and counts the characters in it which are Unicode letters.
The Czech text benchmark reads the Project Gutenberg EBook of *Cítanka pro skoly obecné* by Jan Stastný and Jan Lepar and Josef Sokol (this was to exercise testing against a Latin-alphabet text with lots of diacriticals). 
All letters are counted in the first benchmark and lowercase letters only are counted in the second.
The English text benchmark reads the Project Gutenberg eBook of *Frankenstein* by Mary Wollstonecraft Shelley (to run against a text which is pure ASCII).
All letters and lowercase letters are counted in two benchmarks as with the Czech text. The source code check is from neovim. Again, letters and lowercase letters are counted in the sample.

I compared against [unicode_categories](https://docs.rs/unicode_categories/latest/unicode_categories/) 0.1.1. All times are in ms. Smaller is better.

| Benchmark                | `finl_unicode`              | `unicode_categories`     |
|--------------------------|-----------------------------|--------------------------|
| Japanese text            | 0.26318/**0.26356**/0.26397 | 11.055/**11.071**/11.088 |
| Czech text               | 0.07618/**0.07631**/0.07645 | 2.6268/**2.6293**/2.6316 |
| Czech text (lowercase)   | 0.07601/**0.07614**/0.07626 | 1.4984/**1.4999**/1.5014 |
| English text             | 0.24668/**0.24693**/0.24723 | 11.173/**11.185**/11.195 |
| English text (lowercase) | 0.24682/**0.24707**/0.24735 | 7.8968/**7.9050**/7.9127 |
| Source code              | 0.02738/**0.02745**/0.02753 | 1.5738/**1.5760**/1.5787 |
| Source code (lowercase)  | 0.02733/**0.02735**/0.02738 | 0.7285/**0.7536**/0.7821 | 

As you can see, this is a clear win (the difference is the choice of algorithm. `finl_unicode` uses two-step table lookup to be able to store categories compactly while `unicode_categories` uses a combination of range checks and binary searches on tables).

#### Grapheme clusters

I compared against [unicode_segmentation](https://docs.rs/unicode-segmentation/latest/unicode_segmentation/) 1.9.0 (part of the unicode-rs project) and [bstr](https://docs.rs/bstr/latest/bstr/) 1.0.0. 
Comparisons are run against graphemes.txt, derived from the Unicode test suite, plus several language
texts that were part of the `unicode_segmentation` benchmark suite. 

All times are in µs, smaller is better.

| Benchmark         | `finl_unicde`            | `unicode_segmentation`   | `bstr`                   |
|-------------------|--------------------------|--------------------------|--------------------------|
| Unicode graphemes | 63.692/**63.813**/63.948 | 323.64/**324.08**/324.47 | 273.24/**273.87**/274.63 |
| Arabic text       | 123.67/**124.02**/124.41 | 544.88/**545.97**/547.05 | 1055.7/**1057.8**/1059.8 |
| English text      | 164.48/**164.56**/164.65 | 1057.6/**1061.1**/1064.7 | 349.35/**349.79**/350.26 |
| Hindi text        | 94.467/**94.665**/94.865 | 604.75/**605.38**/606.01 | 838.03/**840.19**/842.23 |
| Japanese text     | 70.491/**70.573**/70.685 | 451.89/**452.88**/453.88 | 997.97/**1000.5**/1003.4 |
| Korean text       | 161.34/**161.79**/162.24 | 600.55/**602.49**/604.49 | 1291.9/**1293.5**/1295.1 |
| Mandarin text     | 67.667/**67.792**/67.941 | 387.86/**388.61**/389.37 | 919.42/**920.86**/922.38 |
| Russian text      | 127.03/**127.30**/127.60 | 609.74/**610.91**/612.12 | 873.43/**877.29**/881.24 |
| Source code       | 176.73/**178.05**/180.91 | 1067.4/**1070.8**/1074.4 | 494.43/**495.96**/497.62 |

With the move from benchmarking on Intel to Apple Silicon, the performance difference for my code versus the other
libraries was generally expanded. I’m curious as to explanations for why this might happen.

## Why not?

You may want to avoid this if you need `no_std` (maybe I’ll cover that in a future version, but probably not). 
If you need other clustering algorithms, I have no near future plans to implement them (but I would do it for money). 

There is no equivalent to `unicode_segmentation`’s `GraphemeCursor` as I don’t need that functionality 
for finl. Reverse iteration over graphemes is not supported, nor do I have plans to support it.

I do not support legacy clustering algorithms which are supported by `unicode-segmentation`. However, the Unicode
specification discourages the use of legacy clustering which is only documented for backwards compatability with very old versions of the Unicode standard.²


## Unicode copyright notice

This package incorporates data from Unicode Inc.
Copyright © 1991–2025 Unicode, Inc. All rights reserved.

## Support

I’ve released this under an MIT/Apache license. Do what you like with it. 
I wouldn’t mind contributions to the ongoing support of developing finl, but they’re not necessary (although if you’re Microsoft or Google and you use my code, surely you can throw some dollars in my bank account).
I guarantee no warranty or support, although if you care to throw some money my way, I can prioritize your requests.

## Version history

- **1.0.0** Initial release
- **1.0.1** Build-process changes to make docs.rs documentation build
- **1.0.2** More changes because the first round apparently weren’t enough
- **1.1.0** Add support for Unicode 15.0.0, added new benchmark comparisons.
- **1.2.0** Allow grapheme clustering to work on any `Peekable` iterator over `char` or `(usize,char)`.
- **1.3.0** Add support for Unicode 16.0.0 (significant changes required for Indic Conjunct clusters), update license documentation and benchmark comparisons.
- **1.4.0** Add support for Unicode 17.0.0

---

1. For technical reasons, the iterator extension returns `Option<String>` rather than `Option<&str>` and thus will autmoatically underperform other implementations which are returning *all* the grapheme clusters. 
For finl, however, I would need an owned value for the string containing the cluster anyway and since I only occasionally need a cluster, I decided it was acceptable to take the performance hit. 
But see the benchmark results for the fact that I apparently managed to implement a faster algorithm anyway when doing an apples-to-apples comparison of speeds. 
2. Pure speculation, but I think that this might be the entire reason for the difference in performance between `finl_unicode` and `unicode_segmentation`. However, I have not looked at the source code to confirm my suspicion.