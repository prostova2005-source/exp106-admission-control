#!/usr/bin/env python3
"""admission_check v2: статическая проверка соответствия трех областей контроля допуска
для правила «только разрешенный реестр образов»:
  D_req - область, где организация требует запрет (пары «ресурс - операция», пространства имен, поля контейнеров);
  Q_int - область, которую фактически перехватывает механизм допуска (пары из каждого правила отдельно,
          с учетом API-группы и версии, и пространства имен, отобранные namespaceSelector);
  L     - логика, применяемая к перехваченным объектам (поля, достижимые из правила violation или из
          выражений validations; префиксы реестров по грамматике имен образов);
  S_old - состояние объектов, существовавших до включения политики (по сохраненному статусу аудита).
Для каждого несоответствия выводятся причина, минимальный контрпример и требуемое изменение.
Ограничения: программа рассчитана на исследованные шаблоны и не выполняет полный разбор Rego/CEL;
готовность контроллера и фактическое поведение при отказе устанавливаются только динамическими тестами."""
import copy, json, re, sys
import yaml

FIELDS = ["containers", "initContainers", "ephemeralContainers"]
Q_REQ = [("", "v1", "pods", "CREATE"), ("", "v1", "pods", "UPDATE"), ("", "v1", "pods/ephemeralcontainers", "UPDATE")]
BAD_IMAGE = "docker.io/library/busybox:1.36"

# ------------------------------------------------------------------ L: достижимость полей
def strip_rego(rego):
    rego = re.sub(r"#.*", "", rego)
    return re.sub(r'"(?:[^"\\]|\\.)*"', '""', rego)          # строки сообщений не учитываются

def rego_rules(rego):
    rules = {}
    for m in re.finditer(r"^([A-Za-z_][\w]*)\s*(\[[^\n]*?\]|\([^\n]*?\))?\s*(?:if\s*)?\{", rego, re.M):
        start = m.end(); depth = 1; i = start
        while i < len(rego) and depth:
            depth += {"{": 1, "}": -1}.get(rego[i], 0); i += 1
        rules.setdefault(m.group(1), []).append(rego[start:i - 1])
    return rules

def fields_rego(rego):
    rules = rego_rules(strip_rego(rego))
    reach, todo = set(), ["violation"]
    while todo:
        n = todo.pop()
        if n in reach or n not in rules: continue
        reach.add(n)
        for body in rules[n]:
            todo += [x for x in re.findall(r"\b([A-Za-z_]\w*)\s*[\[\(]", body) if x in rules]
    body = " ".join(b for n in reach for b in rules[n])
    return {f for f in FIELDS if re.search(r"spec\.%s\[" % f, body)}

def fields_cel(validations):
    exprs = [re.sub(r"'(?:[^'\\]|\\.)*'", "''", v["expression"]) for v in validations]
    return {f for f in FIELDS if any(re.search(r"spec\.%s\b" % f, e) for e in exprs)}

# ------------------------------------------------------------------ Q_int: пары из каждого правила
def res_match(pattern, res):
    if pattern == res or pattern == "*/*": return True
    if pattern == "*": return "/" not in res
    if pattern.endswith("/*"): return res.startswith(pattern[:-1]) and "/" in res
    return False

def intercepted(rules, pair):
    g, v, r, op = pair
    return any((g in x.get("apiGroups", []) or "*" in x.get("apiGroups", [])) and
               (v in x.get("apiVersions", []) or "*" in x.get("apiVersions", [])) and
               (op in x.get("operations", []) or "*" in x.get("operations", [])) and
               any(res_match(p, r) for p in x.get("resources", [])) for x in rules)

def sel_match(sel, labels):
    if sel is None: return True
    for k, v in (sel.get("matchLabels") or {}).items():
        if labels.get(k) != v: return False
    for e in sel.get("matchExpressions") or []:
        k, op, vals = e["key"], e["operator"], e.get("values", [])
        if op == "In" and labels.get(k) not in vals: return False
        if op == "NotIn" and k in labels and labels[k] in vals: return False
        if op == "Exists" and k not in labels: return False
        if op == "DoesNotExist" and k in labels: return False
    return True

# ------------------------------------------------------------------ P: грамматика имени реестра
def registry_prefix_issue(p):
    """Соглашение (нормализация Docker/OCI): первый компонент ссылки является реестром, если содержит
    «.» или «:» или равен localhost; иначе ссылка относится к docker.io. Префикс задается как «реестр/»
    или «реестр/путь/» и обязан оканчиваться «/»."""
    first = p.split("/")[0]
    if not ("." in first or ":" in first or first == "localhost"):
        return "первый компонент «%s» по грамматике имен не является реестром (будет отнесен к docker.io)" % first
    if not p.endswith("/"):
        return "префикс не оканчивается «/», им начинаются и другие имена хостов"
    return None

# ------------------------------------------------------------------ проверка конфигурации
def check(cfg, ns_inventory):
    out = []
    def bad(req, cause, cex, fix): out.append((req, "нарушено", cause, cex, fix))
    def ok(req, note=""): out.append((req, "ok", note, "", ""))
    req_ns = sorted(n for n, l in ns_inventory.items() if cfg["policy_scope"](n, l))
    if cfg["external"]:
        int_ns = sorted(n for n, l in ns_inventory.items() if sel_match(cfg["selector"], l))
    else:
        int_ns = req_ns
    ns0 = req_ns[0] if req_ns else "<нет>"
    # R1
    miss = [f for f in FIELDS if f not in cfg["fields"]]
    if miss:
        f = miss[0]
        cex = ("kubectl debug в %s с --image=%s (UPDATE pods/ephemeralcontainers), запрос перехвачен, но поле не проверяется" % (ns0, BAD_IMAGE)
               if f == "ephemeralContainers" else
               "CREATE pod в %s: %s[0].image=%s, остальные образы из разрешенного реестра" % (ns0, f, BAD_IMAGE))
        bad("R1", "логика не обращается к spec.%s в правилах, достижимых из проверки" % f, cex,
            "добавить проверку spec.%s в логику правила" % f)
    else:
        ok("R1", "все три поля достижимы из логики проверки")
    # R2: пары и пространства имен
    pairs_missing = [p for p in Q_REQ if not intercepted(cfg["rules"], p)]
    gap = sorted(set(req_ns) - set(int_ns))
    if pairs_missing:
        g, v, r, op = pairs_missing[0]
        cex = ("kubectl debug в %s с --image=%s (%s %s)" % (ns0, BAD_IMAGE, op, r) if "ephemeral" in r
               else "%s %s в %s с образом %s" % (op, r, ns0, BAD_IMAGE))
        bad("R2", "не перехватываются пары: " + ", ".join("(%s, %s)" % (p[2], p[3]) for p in pairs_missing),
            cex, "добавить в одно правило resources [%s] и operations [%s]" % (r, op))
    elif gap:
        bad("R2", "пространства имен политики вне области перехвата: " + ", ".join(gap),
            "CREATE pods в %s с образом %s" % (gap[0], BAD_IMAGE),
            "добавить метку или условие namespaceSelector для: " + ", ".join(gap))
    else:
        ok("R2", "Q_req ⊆ Q_int, пространства имен политики перехватываются")
    # R3
    issues = [(p, registry_prefix_issue(p)) for p in cfg["prefixes"]]
    issues = [(p, i) for p, i in issues if i]
    if issues:
        p, i = issues[0]
        if len(issues) > 1: i += "; всего префиксов с ошибкой: %d (%s)" % (len(issues), ", ".join(x for x, _ in issues))
        cex = p + ".evil.example/pause:3.10" if not p.endswith("/") else p.split("/")[0] + "/pause:3.10"
        bad("R3", "префикс «%s»: %s" % (p, i), "CREATE pod в %s с образом %s" % (ns0, cex),
            "задать префикс «%s/»" % p.rstrip("/") if not p.endswith("/") else "указать полное имя реестра")
    else:
        ok("R3", "префиксы соответствуют принятому соглашению об именах")
    # R4
    if not cfg["external"]:
        out.append(("R4", "н/п", "проверка выполняется в API-сервере без внешнего вызова", "", ""))
    elif cfg["failure"] == "Ignore":
        bad("R4", "failurePolicy: Ignore - при недоступном контроллере запрос допускается без проверки",
            "CREATE pod в %s с образом %s при остановленном контроллере" % (ns0, BAD_IMAGE),
            "failurePolicy: Fail вместе с ограничением области перехвата (R5); поведение подтвердить тестом T-down-in")
    else:
        ok("R4", "Fail; фактическое поведение при отказе подтверждается только тестом T-down-in")
    # R5
    excess_ns = sorted(set(int_ns) - set(req_ns))
    excess_res = any(res_match(p, "configmaps") for x in cfg["rules"] for p in x.get("resources", []))
    if cfg["external"] and cfg["failure"] == "Fail" and (excess_ns or excess_res):
        cause = []
        if excess_ns: cause.append("лишние пространства имен: " + ", ".join(excess_ns))
        if excess_res: cause.append("перехватываются ресурсы, не относящиеся к правилу (resources: *)")
        nsx = excess_ns[0] if excess_ns else ns0
        bad("R5", "; ".join(cause),
            "CREATE configmap в %s при остановленном контроллере - отказ failed calling webhook" % nsx,
            "оставить resources [pods, pods/ephemeralcontainers] и namespaceSelector только для: " + ", ".join(req_ns))
    else:
        ok("R5", "при отказе запросы вне области политики не затрагиваются")
    # R6
    st = cfg.get("state")
    if st is None:
        out.append(("R6", "нет данных", "состояние кластера не передано; для VAP аудита нет, нужен отдельный просмотр объектов", "", ""))
    elif st["violations"]:
        v = st["violations"][0]
        bad("R6", "в области политики существуют объекты-нарушители: %d (аудит %s)" % (len(st["violations"]), st["time"]),
            "%s/%s: %s" % (v["namespace"], v["name"], v["image"]),
            "удалить объект или пересоздать его с образом из разрешенного реестра до ввода политики")
    else:
        ok("R6", "аудит %s: нарушений нет" % st["time"])
    return req_ns, int_ns, out

# ------------------------------------------------------------------ загрузка из архива
def gk_cfg(template, constraint, wh, state=None):
    hook = next(x for x in wh["webhooks"] if x["name"] == "validation.gatekeeper.sh")
    params = constraint["spec"]["parameters"]
    scope = constraint["spec"].get("match", {}).get("namespaces")
    return dict(external=True, fields=fields_rego(template["spec"]["targets"][0]["rego"]),
                prefixes=params.get("registries") or params.get("repos"), rules=hook["rules"],
                failure=hook["failurePolicy"], selector=hook.get("namespaceSelector"),
                policy_scope=(lambda n, l, s=scope: (n in s) if s else True), state=state)

def vap_cfg(policy, binding):
    exprs = [v["expression"] for v in policy["spec"]["validations"]]
    sel = binding["spec"].get("matchResources", {}).get("namespaceSelector")
    return dict(external=False, fields=fields_cel(policy["spec"]["validations"]),
                prefixes=sorted(set(re.findall(r"startsWith\('([^']+)'\)", " ".join(exprs)))),
                rules=policy["spec"]["matchConstraints"]["resourceRules"], failure=policy["spec"].get("failurePolicy", "Fail"),
                selector=sel, policy_scope=(lambda n, l, s=sel: sel_match(s, l)), state=None)

def ns_inventory(A, narrow_labels):
    inv = {}
    for line in open(A + "/results/namespaces-labels.txt", encoding="utf8"):
        parts = line.split()
        if len(parts) >= 4 and parts[0].startswith("exp-"):
            inv[parts[0]] = dict(kv.split("=", 1) for kv in parts[3].split(","))
    for n in ("exp-lib", "exp-vap", "default", "kube-system", "kube-public", "kube-node-lease", "gatekeeper-system"):
        inv.setdefault(n, {"kubernetes.io/metadata.name": n})
    inv["exp-vap"]["exp106/vap"] = "true"
    if narrow_labels:
        for n in ("exp-gk", "exp-audit"): inv[n]["exp106/policy"] = "gk"
    return inv

def audit_state(path, time):
    txt = open(path, encoding="utf8").read()
    viol = [dict(image=m.group(1), name=m.group(2), namespace=m.group(3))
            for m in re.finditer(r"image <([^>]+)>.*?\n\s*name:\s*(\S+)\s*\n\s*namespace:\s*(\S+)", txt, re.S)]
    total = re.search(r"totalViolations:\s*(\d+)", txt)
    if total and int(total.group(1)) and not viol:
        viol = [dict(namespace="exp-audit", name="?", image="?")]
    return dict(time=time, violations=viol)

def narrow(wh, fp="Fail", res="pods,pods/ephemeralcontainers", ops="CREATE,UPDATE", scope="narrow", split=False):
    w = copy.deepcopy(wh)
    for h in w["webhooks"]:
        if h["name"] != "validation.gatekeeper.sh": continue
        h["failurePolicy"] = fp
        if scope == "narrow":
            h["rules"] = [{"apiGroups": [""], "apiVersions": ["v1"], "operations": ops.split(","),
                           "resources": res.split(","), "scope": "Namespaced"}]
            if split:   # пример из рецензии: ресурсы разнесены по двум правилам
                h["rules"] = [{"apiGroups": [""], "apiVersions": ["v1"], "operations": ["CREATE", "UPDATE"], "resources": ["pods"]},
                              {"apiGroups": [""], "apiVersions": ["v1"], "operations": ["CREATE"], "resources": ["pods/ephemeralcontainers"]}]
            h.setdefault("namespaceSelector", {}).setdefault("matchExpressions", []).append(
                {"key": "exp106/policy", "operator": "In", "values": ["gk"]})
    return w

def drop_lines(t, word):
    t = copy.deepcopy(t)
    t["spec"]["targets"][0]["rego"] = "\n".join(l for l in t["spec"]["targets"][0]["rego"].splitlines() if word not in l)
    return t

def dead_init(t):
    t = copy.deepcopy(t); tg = t["spec"]["targets"][0]
    tg["rego"] = re.sub(r"input_containers\[c\](\s*\{[^}]*initContainers)", r"unused_init[c]\1", tg["rego"])
    return t

def with_prefixes(c, p):
    c = copy.deepcopy(c); c["spec"]["parameters"]["registries"] = p; return c

if __name__ == "__main__":
    A = sys.argv[1]; M = A + "/manifests"; R = A + "/results"
    Y = lambda p: yaml.safe_load(open(p, encoding="utf8"))
    backup = json.load(open(R + "/additional/webhook-backup.json"))
    T, C = Y(M + "/gatekeeper/template.yaml"), Y(M + "/gatekeeper/constraint.yaml")
    LT, LC = Y(M + "/library/lib-template.yaml"), Y(M + "/library/lib-constraint.yaml")
    LCn = copy.deepcopy(LC); LCn["spec"]["parameters"]["repos"] = ["registry.k8s.io"]
    Cn = copy.deepcopy(C); Cn["spec"]["parameters"]["registries"] = ["registry.k8s.io"]
    st_old = audit_state(R + "/gk-audit-status.txt", "24.10.2026")
    st_new = audit_state(R + "/gk-audit-after-delete.txt", "30.10.2026")
    wide, narrow_inv = ns_inventory(A, False), ns_inventory(A, True)
    cases = [
     ("K1 GK собств., webhook по умолчанию (S2)", gk_cfg(T, C, backup, st_old), wide),
     ("K2 GK собств., широкая область, Fail (W1)", gk_cfg(T, C, json.load(open(R + "/additional/wh-broad-Fail-1794743087306.json")), st_new), wide),
     ("K3 GK собств., ограниченная область, Fail (W2)", gk_cfg(T, C, json.load(open(R + "/additional/wh-narrow-Fail-1794743194221.json")), st_new), narrow_inv),
     ("K4 GK библ., префикс с «/» (S4)", gk_cfg(LT, LC, backup), wide),
     ("K5 GK библ., префикс без «/» (S5)", gk_cfg(LT, LCn, backup), wide),
     ("K6 VAP (S3)", vap_cfg(Y(M + "/vap/vap-policy.yaml"), Y(M + "/vap/vap-binding.yaml")), wide),
     ("M0 контроль", gk_cfg(T, C, narrow(backup), st_new), narrow_inv),
     ("M1 без initContainers", gk_cfg(drop_lines(T, "initContainers"), C, narrow(backup), st_new), narrow_inv),
     ("M2 без ephemeralContainers", gk_cfg(drop_lines(T, "ephemeralContainers"), C, narrow(backup), st_new), narrow_inv),
     ("M3 без pods/ephemeralcontainers", gk_cfg(T, C, narrow(backup, res="pods"), st_new), narrow_inv),
     ("M4 только CREATE", gk_cfg(T, C, narrow(backup, ops="CREATE"), st_new), narrow_inv),
     ("M5 префикс без «/»", gk_cfg(T, Cn, narrow(backup), st_new), narrow_inv),
     ("M6 failurePolicy: Ignore", gk_cfg(T, C, narrow(backup, fp="Ignore"), st_new), narrow_inv),
     ("M7 широкая область при Fail", gk_cfg(T, C, narrow(backup, scope="broad"), st_new), wide),
     ("M8 нарушитель до политики", gk_cfg(T, C, narrow(backup), st_old), narrow_inv),
     ("X1 разнесенные правила (пример рецензии)", gk_cfg(T, C, narrow(backup, split=True), st_new), narrow_inv),
     ("X2 метка exp106/policy только на exp-gk", gk_cfg(T, C, narrow(backup), st_new),
          {**narrow_inv, "exp-audit": {"kubernetes.io/metadata.name": "exp-audit"}}),
     ("X3 initContainers только в неиспользуемом правиле", gk_cfg(dead_init(T), C, narrow(backup), st_new), narrow_inv),
     ("X4 внутренние реестры с портом и localhost", gk_cfg(T, with_prefixes(C, ["registry.local:5000/", "localhost/", "harbor:5000/", "harbor/"]), narrow(backup), st_new), narrow_inv),
    ]
    for name, cfg, inv in cases:
        req_ns, int_ns, res = check(cfg, inv)
        print(name)
        print("   область политики: %s; область перехвата: %s" % (", ".join(req_ns) or "-", ", ".join(int_ns) if len(int_ns) < 5 else "%d пространств имен" % len(int_ns)))
        for r, status, cause, cex, fix in res:
            print("   %s: %s%s" % (r, status, (" - " + cause) if cause else ""))
            if cex: print("       контрпример: " + cex)
            if fix: print("       изменение: " + fix)
