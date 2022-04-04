use std::fmt::{Debug, Display, Formatter};
use std::marker;
use std::mem;
use std::mem::MaybeUninit;
use std::ptr::null_mut;

use rand::{thread_rng, Rng};

/// The maximum height for skip node.
const MAX_HEIGHT: usize = 12;

type SkipTrack<K, V> = [Option<*mut SkipNode<K, V>>; MAX_HEIGHT];

/// A skip list implementation by **unsafe Rust**. **mulit-thread unsafe**, Copy of Leveldb skip list.
///
/// Reference:
/// [LevelDB](https://github.com/google/leveldb)
///
// ANCHOR: struct
pub struct SkipList<K, V> {
    head: *mut SkipNode<K, V>,
    rng: rand::rngs::ThreadRng,
    len: usize,
}

// ANCHOR_END: struct
impl<K: Ord, V> SkipList<K, V> {
    fn random_height(&mut self) -> usize {
        // geometric distribution table
        // f(n) = p^n(1-p), p=0.25
        const RAND_TABLE: [u32; MAX_HEIGHT] = {
            let mut res = [0; MAX_HEIGHT];
            let mut factor = ((u32::MAX as u64) * 3 / 4) as u32;
            let mut i = 1;
            while i < MAX_HEIGHT {
                res[i] = res[i - 1] + factor;
                factor /= 4;
                i += 1;
            }
            res
        };
        let (mut level, rand_num) = (0, self.rng.gen::<u32>());
        while level < RAND_TABLE.len() && rand_num > RAND_TABLE[level] {
            level += 1;
        }
        level
    }
    /// Creates an empty skip list.
    pub fn new() -> Self {
        SkipList {
            // warn: construct a dummy head with entry unconcerned.
            head: Box::into_raw(Box::new(SkipNode {
                entry: unsafe { MaybeUninit::<Entry<K, V>>::uninit().assume_init() },
                next_by_height: [None; MAX_HEIGHT],
            })),
            rng: rand::thread_rng(),
            len: 0,
        }
    }

    fn find(
        &self,
        mut ptr: *mut SkipNode<K, V>,
        level: usize,
        key: &K,
    ) -> (*mut SkipNode<K, V>, bool) {
        unsafe {
            while let Some(next_node) = (*ptr).next_by_height[level] {
                if (*next_node).entry.key > *key {
                    break;
                }
                ptr = next_node;
            }
            (ptr, (*ptr).entry.key == *key)
        }
    }
    /// Gets a reference to the value under the given key.
    pub fn get(&self, key: &K) -> Option<&V> {
        let mut point = self.head;
        for level in (0..MAX_HEIGHT).rev() {
            let (ptr, is_found) = self.find(point, level, key);
            if is_found {
                return Some(unsafe { &(*ptr).entry.value });
            }
            point = ptr;
        }
        None
    }
    /// Returns the number of elements in the skip list.
    pub fn len(&self) -> usize {
        self.len
    }
    /// Gets a mutable reference to the value under the given key.
    pub fn get_mut(&mut self, key: &K) -> Option<&mut V> {
        let mut point = self.head;
        for level in (0..MAX_HEIGHT).rev() {
            let (ptr, is_found) = self.find(point, level, key);
            if is_found {
                return Some(unsafe { &mut (*ptr).entry.value });
            }
            point = ptr;
        }
        None
    }
    /// Puts a key-value pair into the list. Replaces previous value if the same key exists.
    /// Steps are described as following:
    /// 1. search for the closest skip node by key.
    /// 2. if searched same key. replace and return.
    /// 3. else, create a new skip node and insert to proper location.
    pub fn insert(&mut self, key: K, value: V) {
        let jump_height = self.random_height();
        let mut cached = [null_mut(); MAX_HEIGHT];
        let mut start_point = self.head;
        for level in (0..MAX_HEIGHT).rev() {
            let (ptr, is_found) = self.find(start_point, level, &key);
            if is_found {
                unsafe { (*ptr).entry = Entry { key, value } };
                return;
            }
            start_point = ptr;
            cached[level] = ptr;
        }
        let new_node_ptr = Box::into_raw(Box::new(SkipNode {
            entry: Entry { key, value },
            next_by_height: [None; MAX_HEIGHT],
        }));
        cached
            .iter()
            .enumerate()
            .take(jump_height)
            .for_each(|(i, &skip_node)| unsafe {
                (*new_node_ptr).next_by_height[i] = (*skip_node).next_by_height[i];
                (*skip_node).next_by_height[i].replace(new_node_ptr);
            });
        self.len += 1;
    }
    /// Removes the entry from the list.
    pub fn remove(&mut self, key: &K) -> Option<Entry<K, V>> {
        let mut cached: Vec<*mut SkipNode<K, V>> = Vec::new();
        let mut start_point = self.head;
        for level in (0..MAX_HEIGHT).rev() {
            let mut is_found = false;
            unsafe {
                while let Some(next_node) = (*start_point).next_by_height[level] {
                    let k = &(*next_node).entry.key;
                    if k > key {
                        break;
                    } else if k == key {
                        is_found = true;
                        break;
                    }
                    start_point = next_node;
                }
            }
            if is_found {
                cached.push(start_point);
            }
        }
        if cached.is_empty() {
            None
        } else {
            self.len -= 1;
            let to_remove_ptr = unsafe { (*cached[0]).next_by_height[0].unwrap() };
            cached
                .iter()
                .enumerate()
                .rev()
                .for_each(|(i, &ptr)| unsafe {
                    (*ptr).next_by_height[i] = (*to_remove_ptr).next_by_height[i];
                    (*to_remove_ptr).next_by_height[i] = None;
                });
            Some(unsafe { Box::from_raw(to_remove_ptr) }.entry)
        }
    }
    /// Remove the first entry under key order.
    pub fn pop_first(&mut self) -> Option<Entry<K, V>> {
        let head_node = unsafe { &mut *self.head };
        head_node.next_by_height[0].take().map(|first_node_ptr| {
            let mut first_node = unsafe { Box::from_raw(first_node_ptr) };
            for (level, transmit_ptr) in first_node.next_by_height.iter_mut().enumerate() {
                head_node.next_by_height[level] = transmit_ptr.take();
            }
            self.len -= 1;
            first_node.entry
        })
    }
    /// Creates a consuming iterator yielding key-value tuple in specifi order.
    pub fn into_iter(self) -> IntoIterator<K, V> {
        IntoIterator { list: self }
    }
    /// Creates an anonymous iterator yielding the key in specific order.
    pub fn keys(&self) -> impl Iterator<Item = &K> {
        self.iter().map(|(key, _)| key)
    }
    /// Creates an anonymous iterator yielding the values in specific order.
    pub fn values(&self) -> impl Iterator<Item = &V> {
        self.iter().map(|(_, value)| value)
    }
    /// Creates an anonymous iterator yielding the values within range [key1, key2).
    pub fn range(&self, key1: K, key2: K) -> impl Iterator<Item = (&K, &V)> {
        self.iter()
            .filter(move |(key, _)| (*key >= &key1) && (*key < &key2))
    }
    /// Indicates whether the SkipList is empty.
    pub fn is_empty(&self) -> bool {
        self.len == 0
    }
    /// Gets an iterator over the list, sorted by key.
    pub fn iter(&self) -> Iter<K, V> {
        Iter {
            ptr: unsafe { (*self.head).next_by_height[0] },
            _marker1: Default::default(),
            _marker2: Default::default(),
        }
    }
    /// Gets an mutable iterator over the list, sorted by key.
    pub fn iter_mut(&mut self) -> IterMut<K, V> {
        IterMut {
            ptr: unsafe { (*self.head).next_by_height[0] },
            _marker1: Default::default(),
            _marker2: Default::default(),
        }
    }
    /// Clear self
    pub fn clear(&mut self) {
        self.len = 0;
        self.rng = thread_rng();
        let mut ptr = self.head;
        unsafe {
            while let Some(next_ptr) = (*ptr).next_by_height[0].take() {
                Box::from_raw(ptr);
                ptr = next_ptr;
            }
            Box::from_raw(ptr)
        };

        self.head = Box::into_raw(Box::new(SkipNode {
            entry: unsafe { MaybeUninit::<Entry<K, V>>::uninit().assume_init() },
            next_by_height: [None; MAX_HEIGHT],
        }));
    }
}

impl<K, V> Display for SkipList<K, V> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "SkipList:\n {:?}", self.head)
    }
}

impl<K, V> Drop for SkipList<K, V> {
    fn drop(&mut self) {
        let mut ptr = self.head;
        unsafe {
            while let Some(next_ptr) = (*ptr).next_by_height[0].take() {
                if ptr == self.head {
                    // self.head is a dummy node, deconstruct it will cause memory error.
                    mem::forget(ptr)
                }
                else {
                    Box::from_raw(ptr);
                }
                ptr = next_ptr;
            }
            Box::from_raw(ptr);
        };
    }
}

pub struct IterMut<'a, K, V> {
    ptr: Option<*mut SkipNode<K, V>>,
    _marker1: marker::PhantomData<&'a K>,
    _marker2: marker::PhantomData<&'a V>,
}

pub struct Iter<'a, K, V> {
    ptr: Option<*mut SkipNode<K, V>>,
    _marker1: marker::PhantomData<&'a K>,
    _marker2: marker::PhantomData<&'a V>,
}

pub struct IntoIterator<K, V> {
    list: SkipList<K, V>,
}

impl<'a, K, V: 'a> Iterator for IterMut<'a, K, V> {
    type Item = (&'a mut K, &'a mut V);
    fn next(&mut self) -> Option<Self::Item> {
        self.ptr.map(|node| unsafe {
            self.ptr = (*node).next_by_height[0];
            (&mut (*node).entry.key, &mut (*node).entry.value)
        })
    }
}

impl<'a, K, V: 'a> Iterator for Iter<'a, K, V> {
    type Item = (&'a K, &'a V);

    fn next(&mut self) -> Option<Self::Item> {
        self.ptr.map(|node| unsafe {
            self.ptr = (*node).next_by_height[0];
            (&(*node).entry.key, &(*node).entry.value)
        })
    }
}

impl<K, V> Iterator for IntoIterator<K, V>
where
    K: Ord,
{
    type Item = (K, V);
    fn next(&mut self) -> Option<Self::Item> {
        self.list.pop_first().map(Entry::into_tuple)
    }
}

pub struct Entry<K, V> {
    key: K,
    value: V,
}

impl<K, V> Entry<K, V> {
    pub fn into_tuple(self) -> (K, V) {
        (self.key, self.value)
    }
}

impl<K: Ord + Debug, V: Debug> Debug for SkipList<K, V> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        f.debug_map()
            .entries(self.iter().map(|(k, v)| (k, v)))
            .finish()
    }
}

struct SkipNode<K, V> {
    entry: Entry<K, V>,
    next_by_height: SkipTrack<K, V>,
}

#[cfg(test)]
mod tests {
    use std::cmp::Ordering;
    use std::collections::BTreeMap;
    use std::time::Instant;

    use rand::RngCore;

    use super::*;

    fn create_testee() -> SkipList<String, i32> {
        let mut list = SkipList::new();
        let test_case = [("c", 4i32), ("e", 5i32), ("a", 3), ("a", 8)];
        test_case
            .iter()
            .for_each(|&(k, v)| list.insert(k.to_owned(), v));
        list
    }

    #[test]
    fn insert() {
        let list = create_testee();
        let res: Vec<_> = list.into_iter().collect();
        assert_eq!(
            vec![
                ("a".to_owned(), 8),
                ("c".to_owned(), 4),
                ("e".to_owned(), 5)
            ],
            res
        );
    }

    #[test]
    fn debug_print() {
        let list = create_testee();
        assert_eq!(format!("{:?}", list), "{\"a\": 8, \"c\": 4, \"e\": 5}");
    }

    #[test]
    fn insertion_get() {
        let mut list = create_testee();
        assert_eq!(list.get(&"c".to_owned()), Some(&4));
        assert_eq!(list.get(&"e".to_owned()), Some(&5));
        assert_eq!(list.get(&"x".to_owned()), None);
        list.insert("x".to_owned(), 100);
        assert_eq!(list.get(&"x".to_owned()), Some(&100));
    }

    #[test]
    fn pop_and_into_iter() {
        let mut list = SkipList::new();
        let test_case = [("c", 4), ("e", 5), ("a", 3), ("a", 8)];
        test_case.iter().for_each(|&(k, v)| list.insert(k, v));
        assert_eq!(list.len(), 3);
        assert_eq!(
            list.pop_first().map(|x| Entry::into_tuple(x)),
            Some(("a", 8))
        );
        assert_eq!(
            list.pop_first().map(|x| Entry::into_tuple(x)),
            Some(("c", 4))
        );
        assert_eq!(
            list.pop_first().map(|x| Entry::into_tuple(x)),
            Some(("e", 5))
        );
        assert_eq!(list.pop_first().map(|x| Entry::into_tuple(x)), None);
        assert_eq!(list.pop_first().map(|x| Entry::into_tuple(x)), None);
        assert_eq!(list.len(), 0);
        test_case.iter().for_each(|&(k, v)| list.insert(k, v));
        assert_eq!(list.len(), 3);
        assert_eq!(
            list.into_iter().collect::<Vec<(&str, i32)>>(),
            vec![("a", 8), ("c", 4), ("e", 5)]
        );
    }

    #[test]
    fn test_fn_keys_values() {
        let list = create_testee();
        assert_eq!(
            vec![&"a".to_owned(), &"c".to_owned(), &"e".to_owned()],
            list.keys().collect::<Vec<_>>()
        );
        assert_eq!(vec![&8, &4, &5], list.values().collect::<Vec<&i32>>());
    }

    #[test]
    fn test_get_mut() {
        let mut list = create_testee();
        let ele = list.get_mut(&"a".to_owned()).unwrap();
        *ele = 114514;
        assert_eq!(*list.get_mut(&"a".to_owned()).unwrap(), 114514);
    }

    #[test]
    fn test_insertion_remove() {
        let mut list = create_testee();
        assert_eq!(
            list.keys().collect::<Vec<_>>(),
            vec![&"a".to_owned(), &"c".to_owned(), &"e".to_owned()],
        );
        assert_eq!(list.remove(&"a".to_owned()).unwrap().value, 8i32);
        assert!(list.remove(&"a".to_owned()).is_none());
        assert_eq!(list.remove(&"c".to_owned()).unwrap().value, 4i32);
        assert!(list.remove(&"c".to_owned()).is_none());
    }

    #[test]
    fn test_whether_key_ordered() {
        let mut list = SkipList::new();
        let mut rng = rand::thread_rng();
        (0..70000).for_each(|_| {
            list.insert(rng.next_u64(), rng.next_u64());
        });
        assert!(list
            .into_iter()
            .collect::<Vec<_>>()
            .windows(2)
            .all(|w| w[0] < w[1]))
    }

    // the #[bench] is marked as soft_unstable and could not work, comment it out until stable solution.
    // see issue #64266 <https://github.com/rust-lang/rust/issues/64266>

    // #[bench]
    // fn bench_get_inserts_by_skip_list(bencher: &mut Bencher) {
    //     // prepare a BTreeMap and a SkipList with amount of data.
    //     let mut skip_list = SkipList::new();
    //     let mut rng = rand::thread_rng();
    //     bencher.iter(|| {
    //         (0..1000).for_each(|| {
    //             let (key, value) = (rng.next_u64(), rng.next_u64());
    //             skip_list.insert(key, value);
    //         });
    //         skip_list.clear();
    //     });
    // }
    //
    // #[bench]
    // fn bench_get_inserts_by_btreemap(bencher: &mut Bencher) {
    //     // prepare a BTreeMap and a SkipList with amount of data.
    //     let mut btree_map = BTreeMap::new();
    //     let mut rng = rand::thread_rng();
    //     bencher.iter(|| {
    //         (0..1000).for_each(|| {
    //             let (key, value) = (rng.next_u64(), rng.next_u64());
    //             btree_map.insert(key, value);
    //         });
    //         btree_map.clear();
    //     });
    // }

    #[test]
    fn great_many_inserts_gets() {
        let mut list = SkipList::new();
        let mut btree_map = BTreeMap::new();
        let mut rng = rand::thread_rng();
        let mut b_map_cost = Vec::new();
        let mut skip_list_cost = Vec::new();
        (0..70000)
            .map(|_| (rng.next_u64(), rng.next_u64()))
            .for_each(|(k, v)| {
                let t = Instant::now();
                list.insert(k, v);
                skip_list_cost.push(t.elapsed().as_nanos());
                let t = Instant::now();
                btree_map.insert(k, v);
                b_map_cost.push(t.elapsed().as_nanos());
            });
        assert_eq!(btree_map.iter().cmp(list.iter()), Ordering::Equal);
        assert_eq!(btree_map.len(), list.len());
        let skip_list_mean_cost =
            skip_list_cost.iter().sum::<u128>() / skip_list_cost.len() as u128;
        let btree_map_mean_cost = b_map_cost.iter().sum::<u128>() / b_map_cost.len() as u128;
        println!(
            "SkipList time cost: {} ns, BTreeMap cost {} ns",
            skip_list_mean_cost, btree_map_mean_cost
        );
        assert!(
            skip_list_mean_cost * 2 > btree_map_mean_cost,
            "The performance of SkipList is too bad. SkipList:{} ns, BTreeMap{} ns",
            skip_list_mean_cost,
            btree_map_mean_cost
        );
    }

    #[test]
    fn test_double_free() {
        static mut DROPS: u32 = 0;
        struct S;
        impl Drop for S {
            fn drop(&mut self) {
                unsafe {
                    DROPS += 1;
                }
            }
        }
        let count = 10;
        let mut d = SkipList::new();
        (0..count).for_each(|k| d.insert(k, S));
        core::mem::drop(d);
        unsafe {
            assert_eq!(DROPS, count);
        }
    }
}
