#![no_std]
extern crate alloc;
use alloc::boxed::Box;
use alloc::sync::Arc;
use syscalls::{Domain};
use usr::{bdev};
use create::{CreatePCI,
             CreateAHCI,
             CreateMemBDev, 
             CreateBDevShadow,
             CreateIxgbe, 
             CreateNvme,
             CreateNetShadow,
             CreateNvmeShadow,
             CreateBenchnet,
             CreateBenchnvme,
             CreateXv6FS,
             CreateXv6Net,
             CreateXv6NetShadow, 
             CreateXv6Usr, 
             CreateXv6, 
             CreateDomA, 
             CreateDomB, 
             CreateDomC, 
             CreateDomD, 
             CreateShadow
};

pub trait CreateProxy {
    fn create_domain_proxy(
        &self,
        create_pci: Arc<dyn CreatePCI>,
        create_ahci: Arc<dyn CreateAHCI>,
        create_membdev: Arc<dyn CreateMemBDev>,
        create_bdev_shadow: Arc<dyn CreateBDevShadow>,
        create_ixgbe: Arc<dyn CreateIxgbe>,
        create_nvme: Arc<dyn CreateNvme>,
        create_net_shadow: Arc<dyn create::CreateNetShadow>,
        create_nvme_shadow: Arc<dyn create::CreateNvmeShadow>,
        create_benchnet: Arc<dyn CreateBenchnet>,
        create_benchnvme: Arc<dyn create::CreateBenchnvme>,
        create_xv6fs: Arc<dyn CreateXv6FS>,
        create_xv6net: Arc<dyn create::CreateXv6Net>,
        create_xv6net_shadow: Arc<dyn create::CreateXv6NetShadow>,
        create_xv6usr: Arc<dyn CreateXv6Usr>,
        create_xv6: Arc<dyn CreateXv6>,
        create_dom_a: Arc<dyn CreateDomA>,
        create_dom_b: Arc<dyn CreateDomB>,
        create_dom_c: Arc<dyn CreateDomC>,
        create_dom_d: Arc<dyn CreateDomD>,
        create_shadow: Arc<dyn CreateShadow>) -> (Box<dyn Domain>, Arc<dyn Proxy>);
}

pub trait Proxy: CreatePCI +
                 CreateAHCI +
                 CreateMemBDev +
                 CreateBDevShadow +
                 CreateIxgbe +
                 CreateNetShadow +
                 CreateNvmeShadow +
                 CreateBenchnet +
                 CreateBenchnvme +
                 CreateXv6FS + 
                 CreateXv6Usr + 
                 CreateXv6 + 
                 CreateDomA + 
                 CreateDomB + 
                 CreateDomC + 
                 CreateDomD + 
                 CreateShadow {
    // necessary because rust doesn't support trait object upcasting
    fn as_create_pci(&self) -> Arc<dyn CreatePCI>;
    fn as_create_ahci(&self) -> Arc<dyn CreateAHCI>;
    fn as_create_membdev(&self) -> Arc<dyn CreateMemBDev>;
    fn as_create_bdev_shadow(&self) -> Arc<dyn CreateBDevShadow>;
    fn as_create_ixgbe(&self) -> Arc<dyn CreateIxgbe>;
    fn as_create_nvme(&self) -> Arc<dyn CreateNvme>;
    fn as_create_net_shadow(&self) -> Arc<dyn CreateNetShadow>;
    fn as_create_nvme_shadow(&self) -> Arc<dyn CreateNvmeShadow>;
    fn as_create_benchnet(&self) -> Arc<dyn CreateBenchnet>;
    fn as_create_benchnvme(&self) -> Arc<dyn CreateBenchnvme>;
    fn as_create_xv6fs(&self) -> Arc<dyn CreateXv6FS>;
    fn as_create_xv6net(&self) -> Arc<dyn CreateXv6Net>;
    fn as_create_xv6net_shadow(&self) -> Arc<dyn CreateXv6NetShadow>;
    fn as_create_xv6usr(&self) -> Arc<dyn CreateXv6Usr + Send + Sync>;
    fn as_create_xv6(&self) -> Arc<dyn CreateXv6>;
    fn as_create_dom_a(&self) -> Arc<dyn CreateDomA>;
    fn as_create_dom_b(&self) -> Arc<dyn CreateDomB>;
    fn as_create_dom_c(&self) -> Arc<dyn CreateDomC>;
    fn as_create_dom_d(&self) -> Arc<dyn CreateDomD>;
    fn as_create_shadow(&self) -> Arc<dyn CreateShadow>;
}
