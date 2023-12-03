/*===============================================
  CS:5810 Formal Methods in Software Engineering
  Fall 2023

  Mini Project 3 - Part C

  Your name(s): Example solution
  ===============================================*/

include "Option.dfy"
include "List.dfy"
include "Map.dfy"

import opened M = Map
import opened Option

class UMap<T(!new,==)> {

  // this.entrySet() is the set of all the entries in the map 
  ghost function entrySet(): set<Entry<T>>

  // this.keySet() is the set of all the keys in the map 
  ghost function keySet(): set<int>

  // this.valueSet() is the set of all the values in the map 
  ghost function valueSet(): set<T>

  // A map m is valid iff it contains no repeated elements and
  // every key in m has exactly one associated value (no requires or ensures needed) 
  ghost predicate isValid() 

  // this.hasValue(k) is true iff key k as a value in the map
  ghost predicate hasValue(k: int)

  // this.isEmpty() is true iff the map contains no entries
  predicate isEmpty() 

  // constructor returns a (new) map with an empty set of entries.
  constructor ()

  // this.size() returns the number of entries in the map
  method size() returns (s: nat) 

  // this.get(k) returns the value associated to key k in the map, if any.
  // More precisely, it returns Some(v) if k has an associated value v,
  // and returns None otherwhise.
  method get(k: int) returns (vo: Option<T>)

  // this.put(k, v) changes the map so that key k is associated with value v.
  // Then it returns the value previously associated to k in the map, if any.
  // More precisely, it returns Some(v) if k had an associated value v,
  // and returns None otherwhise.
  method put(k: int, v: T) returns (old_vo: Option<T>)

  // this.remove(k) removes from the map the entry eith key k, if any.
  // Then it returns the value previously associated to k in the map, if any.
  // More precisely, it returns Some(v) if k had an associated value v,
  // and returns None otherwhise.
  method remove(k: int) returns (vo: Option<T>)
}
