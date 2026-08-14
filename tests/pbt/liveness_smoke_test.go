package pbt

import (
	"fmt"
	"sync"
	"testing"
	"time"

	"github.com/jeremiah-masters/dlht"
)

// Liveness canary under oversubscription. Scheduler-driven
// lock-freedom probes need a controlled scheduler we don't have, so this is
// the stand-in: heavy mixed churn with far more goroutines than GOMAXPROCS
// must complete within a generous wall-clock budget. GOMAXPROCS=1 is the
// interesting point, since every BinInTransfer back-off and ResizeReserved
// spin must yield or the run livelocks. On timeout the failure carries all
// goroutine stacks. A pass here is not a lock-freedom proof.
func TestPBTLivenessSmoke(t *testing.T) {
	for _, gmp := range gomaxprocsAxis() {
		t.Run(fmt.Sprintf("GOMAXPROCS=%d", gmp), func(t *testing.T) {
			restore := setGOMAXPROCS(gmp)
			defer restore()

			const hotKeys = 32
			opsPerG := 4_000
			goroutines := 16 * gmp
			if testing.Short() {
				opsPerG = 1_000
			}

			m := dlht.New[uint64, uint64](dlht.Options{InitialSize: 1})
			var wg sync.WaitGroup
			for g := range goroutines {
				wg.Add(1)
				go func(g int) {
					defer wg.Done()
					freshBase := uint64(1<<20 + g*opsPerG)
					for i := 0; i < opsPerG; i++ {
						k := uint64((i*7 + g) % hotKeys)
						switch i % 5 {
						case 0:
							m.Insert(k, k<<32|1)
						case 1:
							m.Get(k)
						case 2:
							m.Put(k, k<<32|2)
						case 3:
							m.Delete(k)
						case 4:
							// Fresh-key insert: keeps resizes coming so the
							// transfer/help paths stay hot.
							m.Insert(freshBase+uint64(i), 1)
						}
					}
				}(g)
			}

			if stacks, ok := waitWithWatchdog(&wg, 2*time.Minute); !ok {
				t.Fatalf("workload did not complete within budget at GOMAXPROCS=%d, possible livelock or deadlock\n%s",
					gmp, stacks)
			}
		})
	}
}
