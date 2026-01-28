use crate::error;
use scroll::ctx::{self};
use scroll::{Pread, Pwrite, SizeWith};

#[repr(C)]
#[derive(Debug, PartialEq, Copy, Clone, Default, Pread, Pwrite, SizeWith)]
pub struct DataDirectory {
    pub virtual_address: u32,
    pub size: u32,
}

pub const SIZEOF_DATA_DIRECTORY: usize = 8;
pub(crate) const NUM_DATA_DIRECTORIES: usize = 16;

impl DataDirectory {
    pub fn parse(bytes: &[u8], offset: &mut usize) -> error::Result<Self> {
        Ok(bytes.gread_with(offset, scroll::LE)?)
    }
}

#[derive(Debug, PartialEq, Copy, Clone)]
pub enum DataDirectoryType {
    ExportTable,
    ImportTable,
    ResourceTable,
    ExceptionTable,
    CertificateTable,
    BaseRelocationTable,
    DebugTable,
    Architecture,
    GlobalPtr,
    TlsTable,
    LoadConfigTable,
    BoundImportTable,
    ImportAddressTable,
    DelayImportDescriptor,
    ClrRuntimeHeader,
}

impl TryFrom<usize> for DataDirectoryType {
    type Error = error::Error;
    fn try_from(value: usize) -> Result<Self, Self::Error> {
        Ok(match value {
            0 => Self::ExportTable,
            1 => Self::ImportTable,
            2 => Self::ResourceTable,
            3 => Self::ExceptionTable,
            4 => Self::CertificateTable,
            5 => Self::BaseRelocationTable,
            6 => Self::DebugTable,
            7 => Self::Architecture,
            8 => Self::GlobalPtr,
            9 => Self::TlsTable,
            10 => Self::LoadConfigTable,
            11 => Self::BoundImportTable,
            12 => Self::ImportAddressTable,
            13 => Self::DelayImportDescriptor,
            14 => Self::ClrRuntimeHeader,
            _ => {
                return Err(error::Error::Malformed(
                    "Wrong data directory index number".into(),
                ));
            }
        })
    }
}

#[derive(Debug, PartialEq, Copy, Clone, Default)]
pub struct DataDirectories {
    pub data_directories: [Option<(usize, DataDirectory)>; NUM_DATA_DIRECTORIES],
}

impl ctx::TryIntoCtx<scroll::Endian> for DataDirectories {
    type Error = error::Error;

    fn try_into_ctx(self, bytes: &mut [u8], ctx: scroll::Endian) -> Result<usize, Self::Error> {
        let offset = &mut 0;
        for opt_dd in self.data_directories {
            if let Some((_, dd)) = opt_dd {
                bytes.gwrite_with(dd, offset, ctx)?;
            } else {
                bytes.gwrite([0_u8; SIZEOF_DATA_DIRECTORY], offset)?;
            }
        }
        Ok(*offset)
    }
}

macro_rules! build_dd_getter {
    ($dd_name:tt, $index:tt) => {
        pub fn $dd_name(&self) -> Option<&DataDirectory> {
            let idx = $index;
            self.data_directories[idx].as_ref().map(|(_, dd)| dd)
        }
    };
}

impl DataDirectories {
    pub fn parse(bytes: &[u8], count: usize, offset: &mut usize) -> error::Result<Self> {
        let mut data_directories = [None; NUM_DATA_DIRECTORIES];
        if count > NUM_DATA_DIRECTORIES {
            return Err(error::Error::Malformed(format!(
                "data directory count ({count}) is greater than maximum number of data directories ({NUM_DATA_DIRECTORIES})"
            )));
        }
        for dir in data_directories.iter_mut().take(count) {
            let dd = DataDirectory::parse(bytes, offset)?;
            let dd = if dd.virtual_address == 0 && dd.size == 0 {
                None
            } else {
                Some((*offset, dd))
            };
            *dir = dd;
        }
        Ok(DataDirectories { data_directories })
    }

    build_dd_getter!(get_export_table, 0);
    build_dd_getter!(get_import_table, 1);
    build_dd_getter!(get_resource_table, 2);
    build_dd_getter!(get_exception_table, 3);
    build_dd_getter!(get_certificate_table, 4);
    build_dd_getter!(get_base_relocation_table, 5);
    build_dd_getter!(get_debug_table, 6);
    build_dd_getter!(get_architecture, 7);
    build_dd_getter!(get_global_ptr, 8);
    build_dd_getter!(get_tls_table, 9);
    build_dd_getter!(get_load_config_table, 10);
    build_dd_getter!(get_bound_import_table, 11);
    build_dd_getter!(get_import_address_table, 12);
    build_dd_getter!(get_delay_import_descriptor, 13);
    build_dd_getter!(get_clr_runtime_header, 14);

    pub fn dirs(&self) -> impl Iterator<Item = (DataDirectoryType, DataDirectory)> {
        self.data_directories
            .into_iter()
            .enumerate()
            // (Index, Option<DD>) -> Option<(Index, DD)> -> (DDT, DD)
            .filter_map(|(i, o)|
                // We should not have invalid indexes.
                // Indeed: `data_directories: &[_; N]` where N is the number
                // of data directories.
                // The `TryFrom` trait for integers to DataDirectoryType
                // takes into account the N possible data directories.
                // Therefore, the unwrap can never fail as long as Rust guarantees
                // on types are honored.
                o.map(|(_, v)| (i.try_into().unwrap(), v)))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use scroll::Pwrite;

    // Taken from `C:\Windows\System32\calc.exe`
    const DATA_DIRECTORIES: DataDirectories = DataDirectories {
        data_directories: [
            None,
            Some((
                16,
                DataDirectory {
                    virtual_address: 14584,
                    size: 160,
                },
            )),
            Some((
                24,
                DataDirectory {
                    virtual_address: 24576,
                    size: 18192,
                },
            )),
            Some((
                32,
                DataDirectory {
                    virtual_address: 20480,
                    size: 264,
                },
            )),
            None,
            Some((
                48,
                DataDirectory {
                    virtual_address: 45056,
                    size: 60,
                },
            )),
            Some((
                56,
                DataDirectory {
                    virtual_address: 13160,
                    size: 112,
                },
            )),
            None,
            None,
            None,
            Some((
                88,
                DataDirectory {
                    virtual_address: 12304,
                    size: 320,
                },
            )),
            None,
            Some((
                104,
                DataDirectory {
                    virtual_address: 12624,
                    size: 328,
                },
            )),
            None,
            None,
            None,
        ],
    };

    // Taken from `C:\Windows\System32\calc.exe`
    const DATA_DIRECTORIES_BYTES: &[u8] = &[
        0, 0, 0, 0, 0, 0, 0, 0, 248, 56, 0, 0, 160, 0, 0, 0, 0, 96, 0, 0, 16, 71, 0, 0, 0, 80, 0,
        0, 8, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 176, 0, 0, 60, 0, 0, 0, 104, 51, 0, 0, 112, 0, 0,
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 16, 48, 0, 0,
        64, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 80, 49, 0, 0, 72, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    ];

    #[test]
    fn parse() {
        let mut offset = 0;
        let data_directories =
            DataDirectories::parse(DATA_DIRECTORIES_BYTES, NUM_DATA_DIRECTORIES, &mut offset)
                .expect("failed to parse data directories");

        assert_eq!(offset, NUM_DATA_DIRECTORIES * SIZEOF_DATA_DIRECTORY);
        assert_eq!(data_directories, DATA_DIRECTORIES);
    }

    #[test]
    fn write() {
        let mut buf = [0_u8; 1024];
        let len = buf
            .pwrite(DATA_DIRECTORIES, 0)
            .expect("failed to write optional header");
        assert_eq!(len, NUM_DATA_DIRECTORIES * SIZEOF_DATA_DIRECTORY);
        assert_eq!(
            DATA_DIRECTORIES_BYTES,
            buf.get(..len).expect("not enough data")
        );
    }

    #[test]
    fn read_and_write_consistent() {
        let data_directories =
            DataDirectories::parse(DATA_DIRECTORIES_BYTES, NUM_DATA_DIRECTORIES, &mut 0)
                .expect("failed to parse data directories");

        let mut buf = [0_u8; 1024];
        let len = buf
            .pwrite(data_directories, 0)
            .expect("failed to write data directories");
        assert_eq!(len, NUM_DATA_DIRECTORIES * SIZEOF_DATA_DIRECTORY);
        assert_eq!(
            DATA_DIRECTORIES_BYTES,
            buf.get(..len).expect("not enough data")
        );
    }
}
