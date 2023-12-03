
/*===============================================
  CS:5810 Formal Methods in Software Engineering
  Fall 2023

  Project 3 -- Part A

  Your name(s): 
  ===============================================*/

include "Option.dfy"
include "List.dfy"

module Map {
  
  import opened L = List
  import opened O = Option

  type Entry<T> = (int, T)

  // Auxiliary function that can be used in contracts
  function key<T>(e: Entry<T>): int
  {
    match e
    case (k, _) =>  k
  }

   // Auxiliary function that can be used in contracts
 function value<T>(e: Entry<T>): T
  {
    match e
    case (_, v) =>  v
  }

  type Map<T> = List<Entry<T>>

  // entries(m) is the set of all the elements stored in m (no contract needed)
  ghost function entries<T(!new)>(m: Map<T>): set<Entry<T>>
  { L.elements(m) }

  // A map m is valid iff it contains no repeated elements and
  // every key in m has exactly one associated value (no contract needed) 
  ghost predicate isValid<T(!new)>(m: Map<T>)
  {
    true // replace this line with your definition
  }

  // For every value type T, emptyMap<T>() is 
  // the empty map of elements of type T
  function emptyMap<T(!new)>(): Map<T> 
  { Nil }

  // isEmpty(m) is true iff m has no entries 
  predicate isEmpty<T>(m: Map<T>)
  { m == Nil }

  // size(m) is the number of entries in m
  function size<T(==)>(m: Map<T>): nat 
  {
    match m
    case Nil => 0
    case Cons(_, t) => 1 + size(t)
  }

  // keys(m) is the set of keys in m's entries
  function keys<T(!new)>(m: Map<T>): set<int>
  {
    match m
    case Nil => {}
    case Cons((k, v), t) => {k} + keys(t)
  }

  // values(m) is the set of values in m's entries
  function values<T(!new)>(m: Map<T>): set<T>
  {
    match m
    case Nil => {}
    case Cons((k, v), t) => {v} + values(t)    
  }

  // get(m, k) is the value associated to key k in m, if any.
  // More precisely, it is Some(v) if k has an associated value v,
  // and is None otherwhise.
  function get<T(!new)>(m: Map<T>, k: int): Option<T>
  {
    match m
    case Nil => None
    case Cons((n, v), t) => 
      if k == n then 
        Some(v) 
      else
        get(t, k)
  }

  // remove(m, k) is the map obtained from m by removing from it
  // the entry with key k, if any.
  function remove<T(!new)>(m: Map<T>, k: int): Map<T>
  {
    match m
    case Nil => Nil
    case Cons((k', v'), t) => 
      if k == k' then
        t 
      else
        var m' := remove(t, k);
        put(m', k', v')
  }

  // put(m, k, v) is the map that associates key k with value v
  // and is othewise identical to m.
  function put<T(!new)>(m: Map<T>, k: int, v: T): Map<T>
  {
    match m
    case Nil => Cons((k, v), Nil)
    case Cons((k', v'), t) => 
      if k != k' then
        Cons((k', v'), put(t, k, v))
      else 
        Cons((k', v), t) 
  }
}


// Test

import opened Option
import opened Map

method test() {
  var m: Map<string>;
  var vo: Option<string>;

  m := emptyMap();            assert isValid(m); assert isEmpty(m);
  m := put(m, 3, "Panda");    assert isValid(m); assert !isEmpty(m); assert entries(m) == { (3, "Panda") };
  m := put(m, 9, "Lion");     assert isValid(m); assert entries(m) == { (3, "Panda"), (9, "Lion") };
  vo := get(m, 3);            assert vo == Some("Panda");
  m := put(m, 3, "Bear");     assert isValid(m); assert entries(m) == { (3, "Bear"), (9, "Lion") };
  vo := get(m, 3);            assert vo == Some("Bear");
  vo := get(m, 9);            assert vo == Some("Lion");
  vo := get(m, 7);            assert vo == None;
  m := remove(m, 3);          assert isValid(m); assert entries(m) == { (9, "Lion") };
  vo := get(m, 3);            assert vo == None;
  vo := get(m, 9);            assert vo == Some("Lion");
} 