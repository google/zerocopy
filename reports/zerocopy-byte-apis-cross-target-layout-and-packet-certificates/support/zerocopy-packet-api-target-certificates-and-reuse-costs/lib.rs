use zerocopy::{FromBytes, IntoBytes, TryFromBytes};
use zerocopy::byteorder::{U16, LE};
#[derive(Debug, PartialEq)] pub enum Error { Header, Flags, Payload, Destination }
pub fn decode_write(src: &[u8], dst: &mut [u8]) -> Result<(u8,usize),Error> {
    if src.len()<6 { return Err(Error::Header); }
    let flags=<[bool;4]>::try_read_from_bytes(&src[..4]).map_err(|_|Error::Flags)?;
    let length=U16::<LE>::read_from_bytes(&src[4..6]).unwrap().get() as usize;
    let payload=src.get(6..6+length).ok_or(Error::Payload)?;
    payload.write_to_prefix(dst).map_err(|_|Error::Destination)?;
    let mask=flags.iter().enumerate().fold(0u8,|m,(i,f)| m | (u8::from(*f)<<i));
    Ok((mask,length))
}
#[unsafe(no_mangle)] pub extern "C" fn check_case(seed:u32,length:u32,dst_len:u32,mode:u32)->u32 {
    if length>64 || dst_len>128 || mode>3 {return 99;}
    let n=length as usize;let d=dst_len as usize;
    let mut src=[0u8;70];for i in 0..4 {src[i]=((seed>>i)&1) as u8;}
    src[4..6].copy_from_slice(&(length as u16).to_le_bytes());
    for i in 0..n {src[6+i]=(seed as u8).wrapping_add(i as u8);}
    if mode==1 {src[2]=2;}
    let size=if mode==3 {5} else if mode==2 && n>0 {5+n} else {6+n};
    let mut dst=[0xA5u8;128];
    let result=decode_write(&src[..size],&mut dst[..d]);
    let wanted=if mode==3 {Err(Error::Header)} else if mode==1 {Err(Error::Flags)} else if mode==2 && n>0 {Err(Error::Payload)} else if d<n {Err(Error::Destination)} else {Ok(((seed&15) as u8,n))};
    if result!=wanted {return 1;}
    for i in 0..128 {
        let expected=if wanted.is_ok() && i<n {(seed as u8).wrapping_add(i as u8)} else {0xA5};
        if dst[i]!=expected {return 2;}
    }
    0
}
#[unsafe(no_mangle)] pub extern "C" fn invalid_flag(byte:u32,index:u32)->u32 {
    if byte>255 || index>3{return 99;}
    let mut src=[0u8;6];src[index as usize]=byte as u8;let mut dst=[0xA5u8;8];
    let expected=if byte<2 {Ok(((byte as u8)<<(index as u8),0))} else {Err(Error::Flags)};
    if decode_write(&src,&mut dst)!=expected || dst!=[0xA5;8] {1} else {0}
}
#[unsafe(no_mangle)] pub extern "C" fn layout(field:u32)->u32 {
    match field {0=>std::mem::size_of::<usize>() as u32,1=>std::mem::size_of::<[bool;4]>() as u32,2=>std::mem::align_of::<[bool;4]>() as u32,3=>std::mem::size_of::<U16<LE>>() as u32,4=>std::mem::align_of::<U16<LE>>() as u32,_=>99}
}
