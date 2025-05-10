use crate::SmolBitSet;
use crate::fmt;

use serde::de::{Deserialize, Deserializer, Visitor};
use serde::ser::{Serialize, Serializer};

struct SmolBitSetVisitor;

macro_rules! visit_from {
    ($($name:ident: $t:ty),+) => {$(
        fn $name<E>(self, v: $t) -> Result<Self::Value, E>
        where
            E: serde::de::Error,
        {
            Ok(SmolBitSet::from(v))
        }
    )*}
}

impl Visitor<'_> for SmolBitSetVisitor {
    type Value = SmolBitSet;

    fn expecting(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
        formatter.write_str("a base 10 representation of a bitset")
    }

    fn visit_str<E>(self, v: &str) -> Result<Self::Value, E>
    where
        E: serde::de::Error,
    {
        v.parse().map_err(|()| E::custom("could not parse bitset"))
    }

    visit_from!(
        visit_u8: u8,
        visit_u16: u16,
        visit_u32: u32,
        visit_u64: u64,
        visit_u128: u128
    );
}

impl<'de> Deserialize<'de> for SmolBitSet {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        deserializer.deserialize_any(SmolBitSetVisitor)
    }
}

impl Serialize for SmolBitSet {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        serializer.serialize_str(self.to_string().as_str())
    }
}
