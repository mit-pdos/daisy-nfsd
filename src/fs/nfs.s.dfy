include "../machine/machine.s.dfy"

module Nfs {
  import opened Machine

  datatype Error =
    | Noent
    | Exist
    | NotDir
    | IsDir
    | Inval
    | FBig
    | NoSpc
    | NameTooLong
    | NotEmpty
    | BadHandle
    | ServerFault
  {
    function method nfs3_code(): uint32
    {
      match this {
        case Noent => 2
        case Exist => 17
        case NotDir => 20
        case IsDir => 21
        case Inval => 22
        case FBig => 27
        case NoSpc => 28
        case NameTooLong => 63
        case NotEmpty => 66
        case BadHandle => 10001
        case ServerFault => 10006
      }
    }
  }

  const NFS3_OK: uint32 := 0

  datatype Result<T> =
    | Ok(v: T)
    | Err(err: Error)
  {
    const ErrBadHandle?: bool := Err? && err.BadHandle?
    const ErrInval?: bool := Err? && err.Inval?
    const ErrNoent?: bool := Err? && err.Noent?
    const ErrIsDir?: bool := Err? && err.IsDir?
    const ErrNotDir?: bool := Err? && err.NotDir?

    // make this a failure-compatible type
    // (these duplicate the methods below with the names Dafny requires)

    predicate method IsFailure()
    {
      this.Err?
    }

    function method PropagateFailure<U>(): Result<U>
      requires IsFailure()
    {
      Err(this.err)
    }

    function method Extract(): T
      requires !IsFailure()
    {
      this.v
    }

    // READ and WRITE are not supposed to return Err(IsDir) but should return
    // Err(Inval) when the file is a directory. IsDirToInval transforms just that error
    // condition, from a more primitive method that uses IsDir.
    function method IsDirToInval(): Result<T>
    {
      match this {
        case Ok(v) => Ok(v)
        case Err(err) => if err.IsDir? then Err(Inval) else Err(err)
      }
    }

    function method err_code(): uint32
    {
      match this {
        case Ok(_) => NFS3_OK
        case Err(err) => err.nfs3_code()
      }
    }
  }
}
