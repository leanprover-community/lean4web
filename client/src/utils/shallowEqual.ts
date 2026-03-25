/** Every key of `A` is in `B` and they have the same value. This is not syymmetric */
export function shallowEqualSubset<T extends Record<string, any>>(A: T, B: T): boolean {
  const keysA = Object.keys(A)
  return keysA.every((key) => A[key] === B[key])
}

export function shallowEqual<T extends Record<string, any>>(A: T, B: T): boolean {
  const keysA = Object.keys(A)
  const keysB = Object.keys(B)
  if (keysA.length !== keysB.length) return false
  return keysA.every((key) => A[key] === B[key])
}
