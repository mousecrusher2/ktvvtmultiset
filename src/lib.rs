use std::{collections::HashMap, hash::RandomState};

pub struct HashMultiSet<T, S = RandomState> {
    data: HashMap<T, Vec<T>, S>,
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn it_works() {
    }
}
