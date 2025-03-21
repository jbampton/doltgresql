// Copyright 2024 Dolthub, Inc.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

package cast

import (
	"github.com/dolthub/doltgresql/server/functions/framework"
	"github.com/dolthub/doltgresql/server/types"
)

// Init initializes all casts in this package.
func Init() {
	initBool()
	initChar()
	initDate()
	initFloat32()
	initFloat64()
	initInt16()
	initInt32()
	initInt64()
	initInternalChar()
	initInterval()
	initJson()
	initJsonB()
	initName()
	initNumeric()
	initOid()
	initRegclass()
	initRegproc()
	initRegtype()
	initText()
	initTime()
	initTimestamp()
	initTimestampTZ()
	initTimeTZ()
	initVarChar()

	// This is a hack to get around import cycles. The types package needs these references for type conversions in
	// some contexts
	types.GetImplicitCast = framework.GetImplicitCast
	types.GetAssignmentCast = framework.GetAssignmentCast
	types.GetExplicitCast = framework.GetExplicitCast
}
