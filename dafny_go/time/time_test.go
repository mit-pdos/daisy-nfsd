package time

import "testing"

func TestUnixTimeNano(t *testing.T) {
	time := TimeUnixNano()
	if time < 0 {
		t.Error("expected positive time")
	}
	if time < 1610000000*1_000_000_000 {
		t.Error("time should be in nanoseconds since epoch")
	}
}
