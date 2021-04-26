package time

import "time"

func TimeUnixNano() uint64 {
	return uint64(time.Now().UnixNano())
}
