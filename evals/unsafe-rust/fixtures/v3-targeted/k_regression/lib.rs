#![allow(dead_code)]

pub mod callback_index {
    pub trait Position {
        fn position(&self) -> usize;
    }

    pub fn read<P: Position>(bytes: &[u8], position: &P) -> u8 {
        unsafe { *bytes.get_unchecked(position.position()) }
    }

    pub fn write<P: Position>(bytes: &mut [u8], position: &P, value: u8) {
        unsafe { *bytes.get_unchecked_mut(position.position()) = value }
    }
}

pub mod local_proof {
    pub fn last(bytes: &[u8]) -> Option<u8> {
        if bytes.is_empty() {
            None
        } else {
            let index = bytes.len() - 1;
            // SAFETY: This is the fast path.
            Some(unsafe { *bytes.get_unchecked(index) })
        }
    }
}

pub mod published_lane {
    pub struct Word(pub [u32; 2]);

    /// Identifies one of the two lanes in `Word`.
    ///
    /// # Safety
    ///
    /// `INDEX` must be less than 2. `NAME` must be `"low"` when `INDEX == 0`
    /// and `"high"` when `INDEX == 1`.
    pub unsafe trait Lane {
        const INDEX: usize;
        const NAME: &'static str;
    }

    pub struct High;

    unsafe impl Lane for High {
        const INDEX: usize = 1;
        const NAME: &'static str = "high";
    }

    pub fn read<L: Lane>(word: &Word) -> u32 {
        unsafe { *word.0.get_unchecked(L::INDEX) }
    }
}
