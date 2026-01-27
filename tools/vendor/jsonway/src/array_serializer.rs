use serde_json::Value;

use object_builder;
use array_builder;

pub trait ArraySerializer {
    fn build(&self, &mut array_builder::ArrayBuilder);

    #[inline]
    fn root(&self) -> Option<&str> {
        None
    }

    #[inline]
    fn meta(&self) -> Option<object_builder::ObjectBuilder> {
        None
    }

    fn serialize(&mut self, include_root: bool) -> Value {
        let mut bldr = array_builder::ArrayBuilder::new();

        let root = self.root();
        if include_root && root.is_some() {
            bldr.root(root.unwrap())
        }

        self.build(&mut bldr);

        match self.meta() {
            Some(meta) => {
                let mut meta_bldr = if bldr.has_root() {
                    object_builder::ObjectBuilder::from_json(bldr.unwrap()).unwrap()
                } else {
                    let mut meta_bldr = object_builder::ObjectBuilder::new();
                    meta_bldr.set("data", bldr.unwrap());
                    meta_bldr
                };
                meta_bldr.set_json("meta", meta.unwrap());
                meta_bldr.unwrap()
            }
            None => bldr.unwrap(),
        }
    }
}