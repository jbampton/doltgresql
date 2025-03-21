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
	"github.com/dolthub/go-mysql-server/sql"

	"github.com/dolthub/doltgresql/server/functions/framework"
	pgtypes "github.com/dolthub/doltgresql/server/types"
)

// initBool handles all casts that are built-in. This comprises only the "From" types.
func initBool() {
	boolExplicit()
	boolAssignment()
}

// boolExplicit registers all explicit casts. This comprises only the "From" types.
func boolExplicit() {
	framework.MustAddExplicitTypeCast(framework.TypeCast{
		FromType: pgtypes.Bool,
		ToType:   pgtypes.Int32,
		Function: func(ctx *sql.Context, val any, targetType *pgtypes.DoltgresType) (any, error) {
			if val.(bool) {
				return int32(1), nil
			} else {
				return int32(0), nil
			}
		},
	})
}

// boolAssignment registers all assignment casts. This comprises only the "From" types.
func boolAssignment() {
	framework.MustAddAssignmentTypeCast(framework.TypeCast{
		FromType: pgtypes.Bool,
		ToType:   pgtypes.BpChar,
		Function: func(ctx *sql.Context, val any, targetType *pgtypes.DoltgresType) (any, error) {
			str := "false"
			if val.(bool) {
				str = "true"
			}
			return handleStringCast(str, targetType)
		},
	})
	framework.MustAddAssignmentTypeCast(framework.TypeCast{
		FromType: pgtypes.Bool,
		ToType:   pgtypes.Name,
		Function: func(ctx *sql.Context, val any, targetType *pgtypes.DoltgresType) (any, error) {
			str := "f"
			if val.(bool) {
				str = "t"
			}
			return handleStringCast(str, targetType)
		},
	})
	framework.MustAddAssignmentTypeCast(framework.TypeCast{
		FromType: pgtypes.Bool,
		ToType:   pgtypes.Text,
		Function: func(ctx *sql.Context, val any, targetType *pgtypes.DoltgresType) (any, error) {
			if val.(bool) {
				return "true", nil
			} else {
				return "false", nil
			}
		},
	})
	framework.MustAddAssignmentTypeCast(framework.TypeCast{
		FromType: pgtypes.Bool,
		ToType:   pgtypes.VarChar,
		Function: func(ctx *sql.Context, val any, targetType *pgtypes.DoltgresType) (any, error) {
			str := "false"
			if val.(bool) {
				str = "true"
			}
			return handleStringCast(str, targetType)
		},
	})
}
