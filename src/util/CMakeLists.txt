add_library(util OBJECT debug.cpp name.cpp name_set.cpp fresh_name.cpp
  exception.cpp interrupt.cpp hash.cpp escaped.cpp bit_tricks.cpp
  safe_arith.cpp ascii.cpp memory.cpp shared_mutex.cpp realpath.cpp
  stackinfo.cpp lean_path.cpp serializer.cpp lbool.cpp
  bitap_fuzzy_search.cpp init_module.cpp thread.cpp memory_pool.cpp
  utf8.cpp name_map.cpp list_fn.cpp null_ostream.cpp file_lock.cpp
  task_queue.cpp timer.cpp
  small_object_allocator.cpp subscripted_name_set.cpp process.cpp
  parser_exception.cpp)
