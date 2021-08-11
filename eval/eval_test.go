package eval

import (
	"bytes"
	"strings"
	"testing"

	"github.com/stretchr/testify/assert"
)

func TestObservationSerialization(t *testing.T) {
	assert := assert.New(t)
	o := Observation{
		Values: KeyValue{"throughput": 0.54},
		Config: KeyValue{"bench": "read", "iterations": float64(5)},
	}
	assert.NoError(o.Values.Validate())
	assert.NoError(o.Config.Validate())

	var b bytes.Buffer
	err := o.Write(&b)
	assert.NoError(err)

	o2, err := ReadObservation(&b)
	assert.NoError(err)
	assert.Equal(o, o2, "should read same observation")
}

func TestKeyValueValidate(t *testing.T) {
	kv := KeyValue{"num": 5}
	assert.Error(t, kv.Validate())

	kv = KeyValue{"num": []float64{3, 4}}
	assert.Error(t, kv.Validate())
}

const sampleBench = `
fs=dnfs
fs-smallfile: 10 3076.1 file/sec
fs-largefile: 100 MB throughput 228.05 MB/s
app-bench 0.322581 app/s
fs=gonfs
fs-smallfile: 10 3435.8 file/sec
fs-largefile: 100 MB throughput 468.26 MB/s
app-bench 0.192308 app/s
fs=linux
fs-smallfile: 10 3952.1 file/sec
fs-largefile: 100 MB throughput 178.16 MB/s
app-bench 0.352113 app/s
`

func TestParseSmallfile(t *testing.T) {
	assert := assert.New(t)
	os := SmallfileBench(10).ParseOutput(
		strings.Split(sampleBench, "\n"),
	)
	assert.Len(os, 3)

	assert.Equal(Observation{
		Values: KeyValue{"val": 3076.1},
		Config: KeyValue{"bench": "smallfile", "start": 10.0, "threads": 10.0},
	}, os[0])

	assert.Equal(3435.8, os[1].Values["val"])
}

func TestParseLargefile(t *testing.T) {
	assert := assert.New(t)
	os := LargefileBench(100).ParseOutput(
		strings.Split(sampleBench, "\n"),
	)
	assert.Len(os, 3)
	assert.Equal(228.05, os[0].Values["val"])
	assert.Equal("largefile", os[0].Config["bench"])
}

func TestParseApp(t *testing.T) {
	assert := assert.New(t)
	os := AppBench().ParseOutput(
		strings.Split(sampleBench, "\n"),
	)
	assert.Len(os, 3)
	assert.Equal(0.352113, os[2].Values["val"])
	assert.Equal("app", os[0].Config["bench"])
}
