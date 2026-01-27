use crate::common::{MAGIC_NUM, MAX_WINDOW_SIZE, MIN_WINDOW_SIZE};
use crate::decoding::errors::{FrameDescriptorError, FrameHeaderError, ReadFrameHeaderError};
use crate::io::Read;

/// Read a single serialized frame from the reader and return a tuple containing the parsed frame and the number of bytes read.
pub fn read_frame_header(mut r: impl Read) -> Result<(FrameHeader, u8), ReadFrameHeaderError> {
    use ReadFrameHeaderError as err;
    let mut buf = [0u8; 4];

    r.read_exact(&mut buf).map_err(err::MagicNumberReadError)?;
    let mut bytes_read = 4;
    let magic_num = u32::from_le_bytes(buf);

    // Skippable frames have a magic number in this interval
    if (0x184D2A50..=0x184D2A5F).contains(&magic_num) {
        r.read_exact(&mut buf)
            .map_err(err::FrameDescriptorReadError)?;
        let skip_size = u32::from_le_bytes(buf);
        return Err(ReadFrameHeaderError::SkipFrame {
            magic_number: magic_num,
            length: skip_size,
        });
    }

    if magic_num != MAGIC_NUM {
        return Err(ReadFrameHeaderError::BadMagicNumber(magic_num));
    }

    r.read_exact(&mut buf[0..1])
        .map_err(err::FrameDescriptorReadError)?;
    let desc = FrameDescriptor(buf[0]);

    bytes_read += 1;

    let mut frame_header = FrameHeader {
        descriptor: FrameDescriptor(desc.0),
        dict_id: None,
        frame_content_size: 0,
        window_descriptor: 0,
    };

    if !desc.single_segment_flag() {
        r.read_exact(&mut buf[0..1])
            .map_err(err::WindowDescriptorReadError)?;
        frame_header.window_descriptor = buf[0];
        bytes_read += 1;
    }

    let dict_id_len = desc.dictionary_id_bytes()? as usize;
    if dict_id_len != 0 {
        let buf = &mut buf[..dict_id_len];
        r.read_exact(buf).map_err(err::DictionaryIdReadError)?;
        bytes_read += dict_id_len;
        let mut dict_id = 0u32;

        #[allow(clippy::needless_range_loop)]
        for i in 0..dict_id_len {
            dict_id += (buf[i] as u32) << (8 * i);
        }
        if dict_id != 0 {
            frame_header.dict_id = Some(dict_id);
        }
    }

    let fcs_len = desc.frame_content_size_bytes()? as usize;
    if fcs_len != 0 {
        let mut fcs_buf = [0u8; 8];
        let fcs_buf = &mut fcs_buf[..fcs_len];
        r.read_exact(fcs_buf)
            .map_err(err::FrameContentSizeReadError)?;
        bytes_read += fcs_len;
        let mut fcs = 0u64;

        #[allow(clippy::needless_range_loop)]
        for i in 0..fcs_len {
            fcs += (fcs_buf[i] as u64) << (8 * i);
        }
        if fcs_len == 2 {
            fcs += 256;
        }
        frame_header.frame_content_size = fcs;
    }

    Ok((frame_header, bytes_read as u8))
}

/// A frame header has a variable size, with a minimum of 2 bytes, and a maximum of 14 bytes.
pub struct FrameHeader {
    pub descriptor: FrameDescriptor,
    /// The `Window_Descriptor` field contains the minimum size of a memory buffer needed to
    /// decompress the entire frame.
    ///
    /// This byte is not included in the frame header when the `Single_Segment_flag` is set.
    ///
    /// Bits 7-3 refer to the `Exponent`, where bits 2-0 refer to the `Mantissa`.
    ///
    /// To determine the size of a window, the following formula can be used:
    /// ```text
    /// windowLog = 10 + Exponent;
    /// windowBase = 1 << windowLog;
    /// windowAdd = (windowBase / 8) * Mantissa;
    /// Window_Size = windowBase + windowAdd;
    /// ```
    /// <https://github.com/facebook/zstd/blob/dev/doc/zstd_compression_format.md#window_descriptor>
    window_descriptor: u8,
    /// The `Dictionary_ID` field contains the ID of the dictionary to be used to decode the frame.
    /// When this value is not present, it's up to the decoder to know which dictionary to use.
    dict_id: Option<u32>,
    /// The size of the original/uncompressed content.
    frame_content_size: u64,
}

impl FrameHeader {
    /// Read the size of the window from the header or the total frame content size,
    /// whichever is defined, returning the size in bytes.
    pub fn window_size(&self) -> Result<u64, FrameHeaderError> {
        if self.descriptor.single_segment_flag() {
            Ok(self.frame_content_size())
        } else {
            let exp = self.window_descriptor >> 3;
            let mantissa = self.window_descriptor & 0x7;

            let window_log = 10 + u64::from(exp);
            let window_base = 1 << window_log;
            let window_add = (window_base / 8) * u64::from(mantissa);

            let window_size = window_base + window_add;

            if window_size >= MIN_WINDOW_SIZE {
                if window_size < MAX_WINDOW_SIZE {
                    Ok(window_size)
                } else {
                    Err(FrameHeaderError::WindowTooBig { got: window_size })
                }
            } else {
                Err(FrameHeaderError::WindowTooSmall { got: window_size })
            }
        }
    }

    /// The ID (if provided) of the dictionary required to decode this frame.
    pub fn dictionary_id(&self) -> Option<u32> {
        self.dict_id
    }

    /// Obtain the uncompressed size (in bytes) of the frame contents.
    pub fn frame_content_size(&self) -> u64 {
        self.frame_content_size
    }
}

/// The first byte is called the `Frame Header Descriptor`, and it describes what other fields
/// are present.
pub struct FrameDescriptor(pub u8);

impl FrameDescriptor {
    /// Read the `Frame_Content_Size_flag` from the frame header descriptor.
    ///
    /// This is a 2 bit flag, specifying if the `Frame_Content_Size` field is present
    /// within the header. It notates the number of bytes used by `Frame_Content_size`
    ///
    /// When this value is is 0, `FCS_Field_Size` depends on Single_Segment_flag.
    /// If the `Single_Segment_flag` field is set in the frame header descriptor,
    /// the size of the `Frame_Content_Size` field of the header is 1 byte.
    /// Otherwise, `FCS_Field_Size` is 0, and the `Frame_Content_Size` is not provided.
    ///
    /// | Flag Value (decimal) | Size of the `Frame_Content_Size` field in bytes |
    /// | -- | -- |
    /// | 0 | 0 or 1 (see above) |
    /// | 1 | 2 |
    /// | 2 | 4 |
    /// | 3 | 8 |
    pub fn frame_content_size_flag(&self) -> u8 {
        self.0 >> 6
    }

    /// This bit is reserved for some future feature, a compliant decoder **must ensure**
    /// that this value is set to zero.
    #[expect(dead_code)]
    pub fn reserved_flag(&self) -> bool {
        ((self.0 >> 3) & 0x1) == 1
    }

    /// If this flag is set, data must be regenerated within a single continuous memory segment.
    ///
    /// In this case, the `Window_Descriptor` byte is skipped, but `Frame_Content_Size` is present.
    /// The decoder must allocate a memory segment equal to or larger than `Frame_Content_Size`.
    pub fn single_segment_flag(&self) -> bool {
        ((self.0 >> 5) & 0x1) == 1
    }

    /// If this flag is set, a 32 bit `Content_Checksum` will be present at the end of the frame.
    pub fn content_checksum_flag(&self) -> bool {
        ((self.0 >> 2) & 0x1) == 1
    }

    /// This is a two bit flag telling if a dictionary ID is provided within the header. It also
    /// specifies the size of this field
    ///
    /// | Value (Decimal) | `DID_Field_Size` (bytes) |
    /// | -- | -- |
    /// | 0 | 0 |
    /// | 1 | 1 |
    /// | 2 | 2 |
    /// | 3 | 4 |
    pub fn dict_id_flag(&self) -> u8 {
        self.0 & 0x3
    }

    /// Read the size of the `Frame_Content_size` field from the frame header descriptor, returning
    /// the size in bytes.
    /// If this value is zero, then the `Frame_Content_Size` field is not present within the header.
    pub fn frame_content_size_bytes(&self) -> Result<u8, FrameDescriptorError> {
        match self.frame_content_size_flag() {
            0 => {
                if self.single_segment_flag() {
                    Ok(1)
                } else {
                    Ok(0)
                }
            }
            1 => Ok(2),
            2 => Ok(4),
            3 => Ok(8),
            other => Err(FrameDescriptorError::InvalidFrameContentSizeFlag { got: other }),
        }
    }

    /// Read the size of the `Dictionary_ID` field from the frame header descriptor, returning the size in bytes.
    /// If this value is zero, then the dictionary id is not present within the header,
    /// and "It's up to the decoder to know which dictionary to use."
    pub fn dictionary_id_bytes(&self) -> Result<u8, FrameDescriptorError> {
        match self.dict_id_flag() {
            0 => Ok(0),
            1 => Ok(1),
            2 => Ok(2),
            3 => Ok(4),
            other => Err(FrameDescriptorError::InvalidFrameContentSizeFlag { got: other }),
        }
    }
}
