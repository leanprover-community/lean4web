/** Typing hinter for Object.entries of an interface.
We have some interface `T`, and thus the type of keys/attributes of as `keyof T`.
`[K in keyof T]` is a key of `T` lifted to a type.
`-?` means that the key in the `{...}` object type we are building is required.
`[K, T[K]]` is the type of pairs of the key and its value.
So `{[K in keyof T]-?: [K, T[K]]}` is the type of objects with keys of T
(protomed to types) and values as the tuples of entries of T.
We index into this object with `[keyof T]` to get the pairs of key,value,
and finally with a `[]` to get the array of pairs. */
export type Entries<T> = {
  [K in keyof T]-?: [K, T[K]]
}[keyof T][]
