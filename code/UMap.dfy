/*===============================================
  CS:5810 Formal Methods in Software Engineering
  Fall 2023

  Mini Project 3 - Part C

  Your name(s): Shweta Rajiv and Sage Binder
  ===============================================*/

include "Option.dfy"
include "List.dfy"
include "Map.dfy"

import opened M = Map
import opened Option

class UMap<T(!new,==)> {
  var entries: Map<T>

  // this.entrySet() is the set of all the entries in the map 
  ghost function entrySet(): set<Entry<T>>
    reads this
  {
    M.entries(entries)
  }

  // this.keySet() is the set of all the keys in the map 
  ghost function keySet(): set<int>
    reads this
    requires isValid()
  {
    M.keys(entries)
  }

  // this.valueSet() is the set of all the values in the map 
  ghost function valueSet(): set<T>
    reads this
    requires isValid()
  {
    M.values(entries)
  }

  // A map m is valid iff it contains no repeated elements and
  // every key in m has exactly one associated value (no requires or ensures needed) 
  ghost predicate isValid()
    reads this
  {
    M.isValid(entries)
  }

  // this.hasValue(k) is true iff key k as a value in the map
  ghost predicate hasValue(k: int)
    reads this
    requires isValid()
  {
    k in keySet()
  }

  // this.isEmpty() is true iff the map contains no entries
  predicate isEmpty()
    reads this
    requires isValid()
  {
    entries == List.Nil
  }

  // constructor returns a (new) map with an empty set of entries.
  constructor ()
    ensures isValid()
    ensures isEmpty()
  {
    entries := List.Nil;
  }

  // this.size() returns the number of entries in the map
  method size() returns (s: nat)
    requires isValid()
    ensures s == |entrySet()|
    ensures isValid()
  {
    s := M.size(entries);
  }

  // this.get(k) returns the value associated to key k in the map, if any.
  // More precisely, it returns Some(v) if k has an associated value v,
  // and returns None otherwhise.
  method get(k: int) returns (vo: Option<T>)
    requires isValid()
    ensures k in keySet() ==> exists v :: vo == Some(v) && (k, v) in entrySet()
    ensures k !in keySet() ==> vo == None
    ensures isValid()
  {
    vo := M.get(entries, k);
  }
  // this.put(k, v) changes the map so that key k is associated with value v.
  // Then it returns the value previously associated to k in the map, if any.
  // More precisely, it returns Some(v) if k had an associated value v,
  // and returns None otherwhise.
  method put(k: int, v: T) returns (old_vo: Option<T>)
    modifies this
    requires isValid()
    ensures k in old(keySet()) ==> exists v' :: (k, v') in old(entrySet()) && entrySet() == (old(entrySet())) - {(k, v')} + {(k, v)}
    ensures k !in old(keySet()) ==> entrySet() == old(entrySet()) + {(k, v)}
    ensures isValid()
  {
    old_vo := get(k);
    entries := M.put(entries, k, v);
  }
  // this.remove(k) removes from the map the entry eith key k, if any.
  // Then it returns the value previously associated to k in the map, if any.
  // More precisely, it returns Some(v) if k had an associated value v,
  // and returns None otherwhise.
  method remove(k: int) returns (vo: Option<T>)
    modifies this
    requires isValid()
    ensures k in old(keySet()) ==> exists v :: (k, v) in old(entrySet()) && entrySet() == old(entrySet()) - {(k, v)}
    ensures k !in old(keySet()) ==> entrySet() == old(entrySet())
    ensures isValid()
  {
    vo := get(k);
    entries := M.remove(entries, k);
  }
}
