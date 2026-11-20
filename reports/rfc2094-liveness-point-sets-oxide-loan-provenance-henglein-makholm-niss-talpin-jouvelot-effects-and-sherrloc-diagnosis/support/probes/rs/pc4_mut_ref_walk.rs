// RFC 2094 problem case #4: mutating &mut references while walking a list.
pub struct List<T> { value: T, next: Option<Box<List<T>>> }
pub fn to_refs<T>(mut list: &mut List<T>) -> Vec<&mut T> {
    let mut result = vec![];
    loop {
        result.push(&mut list.value);
        if let Some(n) = list.next.as_mut() {
            list = n;
        } else {
            return result;
        }
    }
}
