/* Copyright 2013-present Barefoot Networks, Inc.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *   http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

/*
 * Antonin Bas (antonin@barefootnetworks.com)
 *
 */

#ifndef BM_PI_PI_H_
#define BM_PI_PI_H_

#include <PI/pi.h>

#include <cstdint>

namespace bm {

class SwitchWContexts;  // forward declaration

namespace pi {

void register_switch(bm::SwitchWContexts *sw, uint32_t cpu_port = 0);

pi_status_t table_idle_timeout_notify(pi_dev_id_t dev_id, pi_p4_id_t table_id,
                                      pi_entry_handle_t entry_handle);

}  // namespace pi

}  // namespace bm

#endif  // BM_PI_PI_H_