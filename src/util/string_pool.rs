use std::collections::HashMap;

use crate::{ir::id::StringId, util::indexed_vec::IndexedVec};

#[derive(Clone, Debug, Default)]
pub struct StringPool {
    lookup: HashMap<String, StringId>,
    strings: IndexedVec<StringId, String>,
}

impl StringPool {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn intern(&mut self, s: impl ToString) -> StringId {
        let s = s.to_string();

        if let Some(id) = self.lookup.get(&s) {
            return *id;
        }

        let id = self.strings.insert(s.clone());
        self.lookup.insert(s, id);
        id
    }

    pub fn get(&self, index: StringId) -> &str {
        &self.strings[index]
    }
}
