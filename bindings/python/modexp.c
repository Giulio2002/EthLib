/*
 * MODEXP precompile wrappers. Each function parses Python arguments,
 * marshals them into Lean runtime objects, invokes the corresponding
 * `@[export]`-d `eth_modexp*` symbol, and unwraps the IO result back to
 * Python.
 */
#include "wrappers.h"

/* ---- Lean externs ----------------------------------------------------- */

extern lean_object*
eth_modexp(
  lean_object* data,
  uint64_t gas
);

extern lean_object*
eth_modexp_gas_cost(
  lean_object* data
);

/* ---- Wrappers --------------------------------------------------------- */

PyObject*
py_modexp(
  PyObject* self,
  PyObject* args
) {
  PyObject *data_obj, *gas_obj;
  if (!PyArg_ParseTuple(args, "OO", &data_obj, &gas_obj)) return NULL;
  if (!PyBytes_Check(data_obj)) {
    PyErr_SetString(PyExc_TypeError, "data must be bytes");
    return NULL;
  }
  /* The gas is a non-negative integer below 2^64. */
  uint64_t gas = (uint64_t) PyLong_AsUnsignedLongLong(gas_obj);
  if (PyErr_Occurred()) return NULL;

  lean_object* res = eth_modexp(
    mk_bytearray((const uint8_t*) PyBytes_AS_STRING(data_obj),
                 (size_t) PyBytes_GET_SIZE(data_obj)),
    gas);
  return run_io_into_pybytes(res, "modexp");
}

PyObject*
py_modexp_gas_cost(
  PyObject* self,
  PyObject* args
) {
  PyObject* data_obj;
  if (!PyArg_ParseTuple(args, "O", &data_obj)) return NULL;
  if (!PyBytes_Check(data_obj)) {
    PyErr_SetString(PyExc_TypeError, "data must be bytes");
    return NULL;
  }
  lean_object* res = eth_modexp_gas_cost(
    mk_bytearray((const uint8_t*) PyBytes_AS_STRING(data_obj),
                 (size_t) PyBytes_GET_SIZE(data_obj)));
  /* The price is returned as big-endian bytes: it can exceed 2^64.
   * The Python package turns it into an `int`. */
  return run_io_into_pybytes(res, "modexp_gas_cost");
}
