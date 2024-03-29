package main

import (
	"flag"
	"fmt"
	"log"
	"net"
	"os"
	"os/signal"
	"runtime"
	"runtime/debug"
	"runtime/pprof"
	"syscall"
	"time"

	"github.com/zeldovich/go-rpcgen/rfc1057"
	"github.com/zeldovich/go-rpcgen/xdr"

	"github.com/mit-pdos/go-journal/util"
	"github.com/mit-pdos/go-nfsd/nfstypes"
	"github.com/mit-pdos/go-nfsd/util/timed_disk"

	"github.com/mit-pdos/daisy-nfsd/nfsd"

	"github.com/tchajed/goose/machine/disk"
)

// Nagle's algorithm. Disabled by default (prioritizing latency over throughput).
var NO_DELAY bool

func pmap_set_unset(prog, vers, port uint32, setit bool) bool {
	var cred rfc1057.Opaque_auth
	cred.Flavor = rfc1057.AUTH_NONE

	pmapc, err := net.Dial("tcp", fmt.Sprintf("localhost:%d", rfc1057.PMAP_PORT))
	if err != nil {
		panic(err)
	}
	err = pmapc.(*net.TCPConn).SetNoDelay(NO_DELAY)
	if err != nil {
		panic(err)
	}
	defer pmapc.Close()
	pmap := rfc1057.MakeClient(pmapc, rfc1057.PMAP_PROG, rfc1057.PMAP_VERS)

	arg := rfc1057.Mapping{
		Prog: prog,
		Vers: vers,
		Prot: rfc1057.IPPROTO_TCP,
		Port: port,
	}

	var res xdr.Bool
	var proc uint32
	if setit {
		proc = rfc1057.PMAPPROC_SET
	} else {
		proc = rfc1057.PMAPPROC_UNSET
	}

	err = pmap.Call(proc, cred, cred, &arg, &res)
	if err != nil {
		panic(err)
	}

	return bool(res)
}

func reportStats(stats []nfsd.OpCount) {
	for _, opCount := range stats {
		op := opCount.Op
		count := opCount.Count
		timeNanos := opCount.TimeNanos
		microsPerOp := float64(timeNanos) / 1e3 / float64(count)
		if count > 0 {
			fmt.Fprintf(os.Stderr,
				"%14s %5d  avg: %0.1f\n",
				op, count, microsPerOp)
		}
	}
}

func logBuildInfo() {
	buildInfo, ok := debug.ReadBuildInfo()
	if !ok {
		log.Printf("Failed to read build info")
		return
	}
	log.Printf("BuildInfo: Main: %+v", buildInfo.Main)
	for _, depmod := range buildInfo.Deps {
		log.Printf("BuildInfo: Dependency: %+v", depmod)
		if depmod.Replace != nil {
			log.Printf("BuildInfo: ---> replaced with: %+v", *depmod.Replace)
		}
	}
}

func main() {
	cpuprofile := flag.String("cpuprofile", "", "write cpu profile to file")
	memprofile := flag.String("memprofile", "", "write mem profile to file")
	mutexprofile := flag.String("mutexprofile", "", "write mutex profile to file")
	blockprofile := flag.String("blockprofile", "", "write block profile to file")

	var diskfile string
	flag.StringVar(&diskfile, "disk", "", "file to store disk in (empty uses MemDisk)")

	var filesizeMegabytes uint64
	flag.Uint64Var(&filesizeMegabytes, "size", 400, "size of file system (in MB)")

	var force bool
	flag.BoolVar(&force, "force", false, "force initialization even if file system seems already initialized")

	var recover bool
	flag.BoolVar(&recover, "recover", false, "run recovery (rather than initialization)")

	var dumpStats bool
	flag.BoolVar(&dumpStats, "stats", false, "dump stats to stderr on exit")

	var asyncWrites bool
	flag.BoolVar(&asyncWrites, "async", false, "enable uncommitted writes (unverified)")

	var printBuildInfo bool
	flag.BoolVar(&printBuildInfo, "build-info", false, "log build info")
	flag.Uint64Var(&util.Debug, "debug", 0, "debug level (higher is more verbose)")

	flag.BoolVar(&NO_DELAY, "no-delay", true, "enable Nagle's algorithm")

	flag.Parse()

	if printBuildInfo {
		logBuildInfo()
	}

	// some extra space to hold the log and file-system metadata
	// (this is in blocks, so it only adds 4MB per 1000 blocks)
	diskBlocks := 1500 + filesizeMegabytes*1024/4

	if *cpuprofile != "" {
		f, err := os.Create(*cpuprofile)
		if err != nil {
			log.Fatal(err)
		}
		pprof.StartCPUProfile(f)
		defer pprof.StopCPUProfile()
	}

	if *memprofile != "" {
		f, err := os.Create(*memprofile)
		if err != nil {
			log.Fatal("could not create memory profile: ", err)
		}
		defer f.Close() // error handling omitted for example
		runtime.GC()    // get up-to-date statistics
		if err := pprof.WriteHeapProfile(f); err != nil {
			log.Fatal("could not write memory profile: ", err)
		}
	}
	if *mutexprofile != "" {
		f, err := os.Create(*mutexprofile)
		if err != nil {
			log.Fatal("could not create mutex profile: ", err)
		}
		runtime.SetMutexProfileFraction(1)
		defer func() {
			mp := pprof.Lookup("mutex")
			if mp != nil {
				mp.WriteTo(f, 0)
			}
			f.Close()
		}()
	}
	if *blockprofile != "" {
		f, err := os.Create(*blockprofile)
		if err != nil {
			log.Fatal("could not create block profile: ", err)
		}
		runtime.SetBlockProfileRate(1)
		defer func() {
			mp := pprof.Lookup("block")
			if mp != nil {
				mp.WriteTo(f, 0)
			}
			f.Close()
		}()
	}

	listener, err := net.ListenTCP("tcp", &net.TCPAddr{})
	if err != nil {
		panic(err)
	}
	port := uint32(listener.Addr().(*net.TCPAddr).Port)

	pmap_set_unset(nfstypes.MOUNT_PROGRAM, nfstypes.MOUNT_V3, 0, false)
	ok := pmap_set_unset(nfstypes.MOUNT_PROGRAM, nfstypes.MOUNT_V3, port, true)
	if !ok {
		panic("Could not set pmap mapping for mount")
	}
	defer pmap_set_unset(nfstypes.MOUNT_PROGRAM, nfstypes.MOUNT_V3, port, false)

	pmap_set_unset(nfstypes.NFS_PROGRAM, nfstypes.NFS_V3, 0, false)
	ok = pmap_set_unset(nfstypes.NFS_PROGRAM, nfstypes.NFS_V3, port, true)
	if !ok {
		panic("Could not set pmap mapping for NFS")
	}
	defer pmap_set_unset(nfstypes.NFS_PROGRAM, nfstypes.NFS_V3, port, false)

	var d disk.Disk
	if diskfile == "" {
		d = disk.NewMemDisk(diskBlocks)
	} else {
		var err error
		d, err = disk.NewFileDisk(diskfile, diskBlocks)
		if err != nil {
			panic("could not create disk file: " + err.Error())
		}
	}
	if dumpStats {
		d = timed_disk.New(d)
	}
	var nfs *nfsd.Nfs
	if recover {
		if diskfile == "" {
			panic("cannot recover from MemDisk")
		}
		start := time.Now()
		nfs = nfsd.RecoverNfs(d)
		dur := time.Since(start).Truncate(10 * time.Millisecond)
		util.DPrintf(1, "recovered daisy-nfsd from disk in %v", dur)
	} else {
		nfs = nfsd.MakeNfs(d, force)
	}
	if nfs == nil {
		panic("could not initialize nfs")
	}
	nfs.SetAsync(asyncWrites)

	srv := rfc1057.MakeServer()
	srv.RegisterMany(nfstypes.MOUNT_PROGRAM_MOUNT_V3_regs(nfs))
	srv.RegisterMany(nfstypes.NFS_PROGRAM_NFS_V3_regs(nfs))

	sigs := make(chan os.Signal, 1)
	signal.Notify(sigs, os.Interrupt)
	go func() {
		<-sigs
		listener.Close()
		if dumpStats {
			fmt.Fprintf(os.Stderr, "\n")
			opCounts := nfs.GetOpStats()
			reportStats(opCounts)
			d.(*timed_disk.Disk).WriteStats(os.Stderr)
		}
	}()
	if dumpStats {
		usrSig := make(chan os.Signal, 1)
		signal.Notify(usrSig, syscall.SIGUSR1)
		go func() {
			for {
				<-usrSig
				opCounts := nfs.GetOpStats()
				nfs.ResetStats()
				reportStats(opCounts)
				d := d.(*timed_disk.Disk)
				d.WriteStats(os.Stderr)
				d.ResetStats()
			}
		}()
	}

	for {
		conn, err := listener.AcceptTCP()
		if err != nil {
			fmt.Printf("accept: %v\n", err)
			break
		}
		err = conn.SetNoDelay(NO_DELAY)
		if err != nil {
			panic(err)
		}

		go srv.Run(conn)
	}
}
