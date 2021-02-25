package debug

import (
	"fmt"
	"os"
)

func Print(s string) {
	fmt.Fprint(os.Stderr, s)
}
