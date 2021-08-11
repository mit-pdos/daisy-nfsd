package eval

import (
	"encoding/json"
	"fmt"
	"io"
	"sort"
)

// KeyValue is a generic set of key-value pairs
//
// expect values to be string, float64, or bool
type KeyValue map[string]interface{}

func (kv KeyValue) Validate() error {
	for key, v := range kv {
		switch v.(type) {
		case string, float64, bool:
			// allowed, fine
			continue
		default:
			return fmt.Errorf("key %v is of type %T and not "+
				"string, float64, or bool", key, v)
		}
	}
	return nil
}

type KeyValuePair struct {
	Key string
	Val interface{}
}

// Pairs returns the key-value pairs in kv, sorted by key
func (kv KeyValue) Pairs() []KeyValuePair {
	var pairs []KeyValuePair
	for key, val := range kv {
		pairs = append(pairs, KeyValuePair{key, val})
	}
	sort.Slice(pairs, func(i int, j int) bool {
		return pairs[i].Key < pairs[j].Key
	})
	return pairs
}

// Delete returns a new KeyValue with key removed
func (kv KeyValue) Delete(key string) KeyValue {
	filtered := kv.Clone()
	delete(filtered, key)
	return filtered
}

func (kv KeyValue) Clone() KeyValue {
	kv2 := make(KeyValue, len(kv))
	for k, v := range kv {
		kv2[k] = v
	}
	return kv2
}

// ExtendPrefixed adds all the pairs in newKv to kv
func (kv KeyValue) ExtendPrefixed(prefix string, newKv KeyValue) {
	for k, v := range newKv {
		kv[prefix+k] = v
	}
}

type Observation struct {
	Values KeyValue `json:"values"`
	Config KeyValue `json:"config"`
}

// Write appends the serialized observation to w
func (o Observation) Write(w io.Writer) error {
	p, err := json.Marshal(o)
	if err != nil {
		return err
	}
	_, err = w.Write(p)
	return err
}

// ReadObservation gets the next observation in r
func ReadObservation(r io.Reader) (o Observation, err error) {
	d := json.NewDecoder(r)
	err = d.Decode(&o)
	return
}

func WriteObservations(w io.Writer, obs []Observation) error {
	for _, o := range obs {
		err := o.Write(w)
		if err != nil {
			return err
		}
	}
	return nil
}
