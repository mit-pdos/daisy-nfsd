include "../../machine/machine.s.dfy"

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

  datatype Result<T> =
    | Ok(v: T)
    | Err(err: Error)
  {
    const ErrBadHandle?: bool := Err? && err.BadHandle?
    const ErrInval?: bool := Err? && err.Inval?
    const ErrNoent?: bool := Err? && err.Noent?
    const ErrIsDir?: bool := Err? && err.IsDir?
    const ErrNotDir?: bool := Err? && err.NotDir?

    function method Coerce<U>(): Result<U>
      requires Err?
    {
      Err(this.err)
    }

    function method Val(): T
      requires this.Ok?
    {
      this.v
    }

    function method err_code(): uint32
    {
      match this {
        case Ok(_) => 0
        case Err(err) => err.nfs3_code()
      }
    }
  }
}
