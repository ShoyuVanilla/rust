pub struct Inner<T> {
    field: T,
}

unsafe impl<T> Send for Inner<T>
where
    T: Copy,
{
}

//@ has nested/struct.Foo.html
//@ has - '//*[@id="synthetic-implementations-list"]//*[@class="impl"]//h3[@class="code-header"]' \
// 'impl<T> Send for Foo<T>where Inner<T>: Send'
//
//@ has - '//*[@id="synthetic-implementations-list"]//*[@class="impl"]//h3[@class="code-header"]' \
// 'impl<T> Sync for Foo<T>where T: Sync'
pub struct Foo<T> {
    inner_field: Inner<T>,
}
