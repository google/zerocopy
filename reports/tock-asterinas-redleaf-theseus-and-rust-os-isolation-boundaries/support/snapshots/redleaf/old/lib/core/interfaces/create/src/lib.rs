#![no_std]
#![feature(associated_type_defaults)]
extern crate alloc;
use alloc::boxed::Box;
use alloc::sync::Arc;
use syscalls::{Heap, Domain, Interrupt};
use usr::{bdev::{BDev, NvmeBDev}, vfs::VFS, usrnet::UsrNet, xv6::Xv6, dom_a::DomA, dom_c::DomC, net::Net, pci::{PCI, PciBar, PciResource}};
use usr::error::Result;

/* AB: XXX: first thing: change all names to create_domain -- it's absurd */
pub trait CreatePCI: Send + Sync {
    fn create_domain_pci(&self) -> (Box<dyn Domain>, Box<dyn PCI>);
}

pub trait CreateAHCI: Send + Sync {
    fn create_domain_ahci(&self, pci: Box<dyn PCI>) -> (Box<dyn Domain>, Box<dyn BDev>);
}

pub trait CreateMemBDev: Send + Sync {
    fn create_domain_membdev(&self, memdisk: &'static mut [u8]) -> (Box<dyn Domain>, Box<dyn BDev>);
    fn recreate_domain_membdev(&self, dom: Box<dyn syscalls::Domain>, memdisk: &'static mut [u8]) -> (Box<dyn Domain>, Box<dyn BDev>);
}

pub trait CreateBDevShadow: Send + Sync {
    fn create_domain_bdev_shadow(&self, create: Arc<dyn CreateMemBDev>) -> (Box<dyn Domain>, Box<dyn BDev>);
}

pub trait CreateIxgbe: Send + Sync {
    fn create_domain_ixgbe(&self, pci: Box<dyn PCI>) -> (Box<dyn Domain>, Box<dyn Net>);
}

pub trait CreateNetShadow: Send + Sync {
    fn create_domain_net_shadow(&self, create: Arc<dyn CreateIxgbe>, pci: Box<dyn PCI>) -> (Box<dyn Domain>, Box<dyn Net>);
}

pub trait CreateNvmeShadow: Send + Sync {
    fn create_domain_nvme_shadow(&self, create: Arc<dyn CreateNvme>, pci: Box<dyn PCI>) -> (Box<dyn Domain>, Box<dyn NvmeBDev>);
}

pub trait CreateNvme: Send + Sync {
    fn create_domain_nvme(&self, pci: Box<dyn PCI>) -> (Box<dyn Domain>, Box<dyn usr::bdev::NvmeBDev>);
}

pub trait CreateXv6FS: Send + Sync {
    fn create_domain_xv6fs(&self, bdev: Box<dyn BDev>) ->(Box<dyn Domain>, Box<dyn VFS>);
}

pub trait CreateXv6Net: Send + Sync {
    fn create_domain_xv6net(&self, net: Box<dyn Net>) ->(Box<dyn Domain>, Box<dyn UsrNet>);
}

pub trait CreateXv6NetShadow: Send + Sync {
    fn create_domain_xv6net_shadow(&self, create: Arc<dyn CreateXv6Net>, net: Box<dyn Net>) ->(Box<dyn Domain>, Box<dyn UsrNet>);
}

pub trait CreateXv6Usr: Send + Sync {
    fn create_domain_xv6usr(&self, name: &str, xv6: Box<dyn usr::xv6::Xv6>, blob: &[u8], args: &str) -> Result<Box<dyn syscalls::Domain>>;
}
pub type CreateXv6UsrPtr = Box<dyn CreateXv6Usr + Send + Sync>;

pub trait CreateXv6: Send + Sync {
    fn create_domain_xv6kernel(&self,
                               ints: Box<dyn Interrupt>,
                               create_xv6fs: Arc<dyn CreateXv6FS>,
                               create_xv6net: Arc<dyn CreateXv6Net>,
                               create_xv6net_shadow: Arc<dyn CreateXv6NetShadow>,
                               create_xv6usr: Arc<dyn CreateXv6Usr + Send + Sync>,
                               bdev: Box<dyn BDev>,
                               net: Box<dyn usr::net::Net>,
                               nvme: Box<dyn usr::bdev::NvmeBDev>) -> (Box<dyn Domain>, Box<dyn Xv6>);
}

pub trait CreateDomA: Send + Sync {
    fn create_domain_dom_a(&self) -> (Box<dyn Domain>, Box<dyn DomA>);
}

pub trait CreateDomB: Send + Sync {
    fn create_domain_dom_b(&self, dom_a: Box<dyn DomA>) -> Box<dyn Domain>;
}

pub trait CreateDomC: Send + Sync {
    fn create_domain_dom_c(&self) -> (Box<dyn Domain>, Box<dyn DomC>);
    fn recreate_domain_dom_c(&self, dom: Box<dyn Domain>) -> (Box<dyn Domain>, Box<dyn DomC>);
}

pub trait CreateDomD: Send + Sync {
    fn create_domain_dom_d(&self, dom_c: Box<dyn DomC>) -> Box<dyn Domain>;
}

pub trait CreateShadow: Send + Sync {
    fn create_domain_shadow(&self, create_dom_c: Arc<dyn CreateDomC>) -> (Box<dyn Domain>, Box<dyn DomC>);
}

pub trait CreateBenchnet: Send + Sync {
    fn create_domain_benchnet(&self, net: Box<dyn Net>) -> Box<dyn Domain>;
}

pub trait CreateBenchnvme: Send + Sync {
    fn create_domain_benchnvme(&self, nvme: Box<dyn NvmeBDev>) -> Box<dyn Domain>;
}

pub trait CreateHashStore: Send + Sync {
    fn create_domain_hashstore(&self) -> Box<dyn Domain>;
}

pub trait CreateTpm: Send + Sync {
    fn create_domain_tpm(&self) -> (Box<dyn Domain>, Box<dyn usr::tpm::TpmDev>);
}
