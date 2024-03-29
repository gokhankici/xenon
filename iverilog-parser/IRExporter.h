#ifndef IR_EXPORTER_H
#define IR_EXPORTER_H

#include <iostream>
#include <vector>
#include <sstream>
#include <cassert>
#include <unordered_set>
#include <unordered_map>

#include "Visitor.h"
#include "ExprVisitor.h"

#include "IRExpr.h"
#include "IRStmt.h"
#include "IRModule.h"

class IRExporter
{
public:
    IRExporter(const IRExporter* top, Module *m) : IRExporter(top, m, NULL) { }

    IRExporter(const IRExporter* top, Module *m, PGModule *mi)
        : module(m), moduleInstantiation(mi)
    {
        if (top) {
            for (auto ire : top->history) {
                history.push_back(ire);
            }
            history.push_back(top);
        }
    }

    // -------------------------------------------------------------------------
    // IR Exporting Functions
    // -------------------------------------------------------------------------
    const IRModule *extractModule() const;
    const IRExpr *toIRExpr(PExpr *) const;
    const IRStmt *toIRStmt(PGate *) const;
    const IRStmt *toIRStmt(Statement *) const;
    const IREvent *toIREvent(PEEvent *) const;
    // -------------------------------------------------------------------------

    // -------------------------------------------------------------------------
    // Helper Functions
    // -------------------------------------------------------------------------
    const std::string getPermString(const perm_string&) const;
    void setModulePorts(IRModule *) const;
    bool isToplevel() const;
    bool isConstantExpr(PExpr *) const;
    const IRExpr *pform_nameToIRExpr(const pform_name_t &that) const;
    const IRExpr *nameComponentToIRExpr(const perm_string &,
                                        const std::list<index_component_t> &) const;
    static bool moduleExists(const std::string &moduleName);
    static void setModule(const std::string &moduleName, const IRModule *irModule);
    // -------------------------------------------------------------------------

    const Module *getModule() const
    {
        return module;
    }

    const PGModule *getModuleInstantiation() const
    {
        return moduleInstantiation;
    }

private:
    const Module *const module;
    const PGModule *const moduleInstantiation;

    static std::unordered_map<std::string, const IRModule *> irModules;

    std::vector<const IRExporter*> history;

    friend std::ostream &operator<<(std::ostream &, const IRExporter &);
};

#endif // PROLOG_EXPORTER_H
