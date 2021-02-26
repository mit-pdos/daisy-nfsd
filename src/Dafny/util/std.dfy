module Std
{
  datatype Option<T> = Some(x:T) | None

  function map_delete<K, V>(m: map<K, V>, k0: K): map<K, V>
  {
    map k: K | k in m && k != k0 :: m[k]
  }

  lemma map_delete_not_in<K, V>(m: map<K, V>, k0: K)
    ensures k0 !in map_delete(m, k0)
  {}

  lemma map_delete_other<K, V>(m: map<K, V>, k0: K, k: K)
    requires k in m && k != k0
    ensures k in map_delete(m, k0) && map_delete(m, k0)[k] == m[k]
  {}
}
