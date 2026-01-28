use super::cover::K;
use alloc::vec::Vec;
use core::f64::consts::E;
use fastrand;
use std::{io, vec};

/// Creates a representative sample of `input` of `size` bytes.
pub fn create_sample<R: io::Read>(input: &mut R, size: usize) -> Vec<u8> {
    let reservoir = Reservoir::new(size);
    reservoir.fill(input)
}

/// A reservoir is created from an input stream.
///
/// Once filled, it will contain a best effort sample of a dataset,
/// where each input value has an equivalent probability of being included.
struct Reservoir {
    /// Where the sampled data is stored.
    ///
    /// Once the lake is filled, then this should contain a representative sample
    /// of the larger dataset.
    lake: Vec<u8>,
    /// K is the size of each sample.
    ///
    /// The original Zstd dictionary implementation states that values
    /// between 16 and 2048+ are reasonable.
    k: u16,
}

impl Reservoir {
    /// Initialize a new empty reservoir, creating an allocation of `size`.
    pub fn new(size: usize) -> Self {
        assert!(size >= 16, "Reservoirs cannot be below 16 bytes in size");
        let lake: Vec<u8> = vec![0; size];
        let k = K as u16;
        Self { lake, k }
    }

    /// Filling the reservoir is performed using Algorithm L.
    ///
    /// The return value is the populated reservoir.
    pub fn fill<R: io::Read>(mut self, source: &mut R) -> Vec<u8> {
        // https://en.wikipedia.org/wiki/Reservoir_sampling#:~:text=end%0A%20%20end%0Aend-,Optimal%3A%20Algorithm,-L%5Bedit
        // https://richardstartin.github.io/posts/reservoir-sampling#algorithm-l:~:text=%3B%0A%20%20%20%20%7D%0A%7D-,Algorithm%20L,-Algorithm%20L%20was

        // First fill the reservoir with the start of the input stream
        let mut total_bytes_read: usize = 0;
        while let Ok(num_bytes) = source.read(self.lake.as_mut_slice()) {
            total_bytes_read += num_bytes;
            // Stop when we've completely filled the buffer
            if total_bytes_read == self.lake.len() {
                break;
            }
            // If we haven't filled the lake all the way, resize it
            if num_bytes == 0 {
                self.lake.resize(total_bytes_read, 0);
            }
        }

        let mut threshold = E.powf(fastrand::f64().ln() / f64::from(self.k));
        // An index into the stream of the next sample to take
        let mut next = self.lake.len();
        // Because we're sampling k-mers of size K into the lake,
        // split the lake into chunks of k size for simplicity
        let mut lake_chunks = self
            .lake
            .chunks_mut(self.k as usize)
            .collect::<Vec<&mut [u8]>>();
        // Used when discarding chunks
        let end_of_lake = lake_chunks.len();
        let mut counter = end_of_lake / self.k as usize;
        // Algorithm L is considered better than algorithm R because it
        // determines how many inputs can be skipped, rather than
        // processing every input.

        // This is done by abusing the statistics in ways
        // I do not understand.

        // Items with a weight smaller than the threshold enter the lake,
        // replacing the item in the lake with the largest threshold

        let mut dumpster = Vec::with_capacity(self.k as usize);
        loop {
            // `num_bytes_read` is kept track of to watch for EOD.
            let num_bytes_read: u64;
            if counter == next {
                num_bytes_read = source
                    .read(lake_chunks[fastrand::usize(0..end_of_lake)])
                    .unwrap() as u64;
                // Advance at least to the next sample, skipping forward a few samples
                next += ((fastrand::f64().ln() / f64::ln(1.0 - threshold)).floor() as usize + 1)
                    * self.k as usize;
                // Update the threshold to reflect changes
                threshold *= E.powf(fastrand::f64().ln() / f64::from(end_of_lake as u32))
            } else {
                // Drop the next chunk
                num_bytes_read = source.read(&mut dumpster).unwrap() as u64;
                //source.seek_relative(self.k.into()).unwrap();
            }
            if num_bytes_read == 0 {
                break;
            }
            counter += self.k as usize;
        }
        self.lake.shrink_to_fit();
        self.lake
    }
}

#[cfg(test)]
mod tests {
    use super::Reservoir;
    use alloc::vec;

    #[test]
    fn initial_fill() {
        // Create a reservoir 16 bytes in size and read
        // 16 bytes into it
        let r = Reservoir::new(16);
        let test_data = vec![0_u8; 16];
        let output = r.fill(&mut test_data.as_slice());
        assert_eq!(test_data, output);
    }

    #[test]
    fn shrinks_for_small_sample() {
        // Create a reservoir larger than the sample.
        // The output should be smaller.
        let r = Reservoir::new(32);
        let test_data = vec![0_u8; 28];
        let output = r.fill(&mut test_data.as_slice());
        assert!(output.len() == 28);
    }

    #[test]
    fn lake_doesnt_grow() {
        // Create a sample larger than the reservoir
        // The output should be smaller.
        let r = Reservoir::new(32);
        let test_data = vec![0_u8; 16_000_000];
        let output = r.fill(&mut test_data.as_slice());
        assert!(output.len() == 32);
    }
}
