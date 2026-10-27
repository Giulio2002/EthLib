/* XMSS wrappers around the `eth_xmss_*` Lean exports. */
#include "wrappers.h"

/* ---- Lean externs ----------------------------------------------------- */

/* Each export consumes its object arguments, so the caller never releases them. */

extern lean_object*
eth_xmss_key_gen(
  lean_object* seed,
  uint32_t epoch_start,
  uint32_t epoch_end
);

extern lean_object*
eth_xmss_sign(
  lean_object* seed,
  uint32_t epoch_start,
  uint32_t epoch_end,
  uint32_t epoch,
  lean_object* msg
);

extern lean_object*
eth_xmss_verify(
  lean_object* pk,
  uint32_t epoch,
  lean_object* msg,
  lean_object* sig
);

/* ---- Local helpers (XMSS-only) --------------------------------------- */

/* Read a Python int in [0, max]; returns 0 on success. */
static int
parse_uint(
  PyObject* obj,
  unsigned long max,
  const char* name,
  unsigned long* out
) {
  if (!PyLong_Check(obj)) {
    PyErr_Format(PyExc_TypeError, "%s: expected int", name);
    return 1;
  }
  unsigned long v = PyLong_AsUnsignedLong(obj);
  if (v == (unsigned long) -1 && PyErr_Occurred()) return 1;
  if (v > max) {
    PyErr_Format(PyExc_OverflowError, "%s: must be at most %lu, got %lu",
                 name, max, v);
    return 1;
  }
  *out = v;
  return 0;
}

/* ---- Wrappers --------------------------------------------------------- */

PyObject*
py_xmss_key_gen(
  PyObject* self,
  PyObject* args
) {
  PyObject *seed_obj, *start_obj, *end_obj;
  if (!PyArg_ParseTuple(args, "OOO", &seed_obj, &start_obj, &end_obj)) return NULL;
  const uint8_t* seed = parse_bytes_of_size(seed_obj, XMSS_SEED_LEN, "seed");
  if (!seed) return NULL;
  unsigned long start, end;
  if (parse_uint(start_obj, UINT32_MAX, "epoch_start", &start)) return NULL;
  if (parse_uint(end_obj, UINT32_MAX, "epoch_end", &end)) return NULL;

  uint8_t out[XMSS_PUB_KEY_SIZE];
  lean_object* res = eth_xmss_key_gen(
    mk_bytearray(seed, XMSS_SEED_LEN), (uint32_t) start, (uint32_t) end);
  if (run_io_into_bytearray(res, out, XMSS_PUB_KEY_SIZE)) {
    PyErr_SetString(PyExc_RuntimeError, "key_gen failed");
    return NULL;
  }
  return PyBytes_FromStringAndSize((const char*) out, XMSS_PUB_KEY_SIZE);
}

PyObject*
py_xmss_sign(
  PyObject* self,
  PyObject* args
) {
  PyObject *seed_obj, *start_obj, *end_obj, *epoch_obj, *msg_obj;
  if (!PyArg_ParseTuple(args, "OOOOO",
        &seed_obj, &start_obj, &end_obj, &epoch_obj, &msg_obj)) return NULL;
  const uint8_t* seed = parse_bytes_of_size(seed_obj, XMSS_SEED_LEN, "seed");
  if (!seed) return NULL;
  unsigned long start, end, epoch;
  if (parse_uint(start_obj, UINT32_MAX, "epoch_start", &start)) return NULL;
  if (parse_uint(end_obj, UINT32_MAX, "epoch_end", &end)) return NULL;
  if (parse_uint(epoch_obj, UINT32_MAX, "epoch", &epoch)) return NULL;
  const uint8_t* msg = parse_bytes_of_size(msg_obj, XMSS_MESSAGE_LEN, "message");
  if (!msg) return NULL;

  uint8_t out[XMSS_SIG_SIZE];
  lean_object* res = eth_xmss_sign(
    mk_bytearray(seed, XMSS_SEED_LEN),
    (uint32_t) start, (uint32_t) end, (uint32_t) epoch,
    mk_bytearray(msg, XMSS_MESSAGE_LEN));
  if (run_io_into_bytearray(res, out, XMSS_SIG_SIZE)) {
    PyErr_SetString(PyExc_RuntimeError, "sign failed");
    return NULL;
  }
  return PyBytes_FromStringAndSize((const char*) out, XMSS_SIG_SIZE);
}

PyObject*
py_xmss_verify(
  PyObject* self,
  PyObject* args
) {
  PyObject *pk_obj, *epoch_obj, *msg_obj, *sig_obj;
  if (!PyArg_ParseTuple(args, "OOOO", &pk_obj, &epoch_obj, &msg_obj, &sig_obj)) return NULL;
  const uint8_t* pk = parse_bytes_of_size(pk_obj, XMSS_PUB_KEY_SIZE, "public key");
  if (!pk) return NULL;
  unsigned long epoch;
  if (parse_uint(epoch_obj, UINT32_MAX, "epoch", &epoch)) return NULL;
  const uint8_t* msg = parse_bytes_of_size(msg_obj, XMSS_MESSAGE_LEN, "message");
  if (!msg) return NULL;
  const uint8_t* sig = parse_bytes_of_size(sig_obj, XMSS_SIG_SIZE, "signature");
  if (!sig) return NULL;

  uint8_t ok = 0;
  lean_object* res = eth_xmss_verify(
    mk_bytearray(pk, XMSS_PUB_KEY_SIZE),
    (uint32_t) epoch,
    mk_bytearray(msg, XMSS_MESSAGE_LEN),
    mk_bytearray(sig, XMSS_SIG_SIZE));
  if (run_io_into_bool(res, &ok)) {
    PyErr_SetString(PyExc_RuntimeError, "verify failed");
    return NULL;
  }
  if (ok) Py_RETURN_TRUE; else Py_RETURN_FALSE;
}
