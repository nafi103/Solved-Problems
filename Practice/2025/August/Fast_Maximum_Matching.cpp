#include<bits/stdc++.h>
#include<ext/pb_ds/assoc_container.hpp>
#include<ext/pb_ds/tree_policy.hpp>

using namespace std;
using namespace chrono;
using namespace __gnu_pbds;

/****************************************************************/

#define int long long
#define pi acos(-1.0)
const int mod = 998244353;
#define inf 1e18+10
#define pb push_back
#define ff first
#define ss second
#define sz(x) (int)(x).size()
#define LSOne(x) ((x)&(-x))
#define all(x) x.begin(), x.end()
#define readv(v)      \
    for (auto &x : v) \
    cin >> x
#define writev(v)     \
    for (auto &x : v) \
    cout << x << " "; \
    cout<<endl
#define endl "\n"
#define yes cout<<"YES"<<endl
#define no cout<<"NO"<<endl
#define remove_punctuation(text) regex_replace(text, regex(R"([^\w\s])"), "")
#define fastIO ios::sync_with_stdio(false), cin.tie(nullptr), cout.tie(nullptr)
template <class T> using pbds = tree<T, null_type, less<T>, rb_tree_tag, tree_order_statistics_node_update >;

#ifndef ONLINE_JUDGE
#include "debug.h"
#define debug(x) cerr << #x << " = "; _print(x); cerr << endl;
#else
#define debug(...)
#endif

mt19937 rng(chrono::steady_clock::now().time_since_epoch().count());
/****************************************************************/
vector<vector<int>> g;
vector<int> pairU, pairV, dist;

static const int INF_DIST = 1e9;

bool bfs(int n) {
    queue<int> q;
    for (int u = 0; u < n; ++u) {
        if (pairU[u] == -1) {
            dist[u] = 0;
            q.push(u);
        } else {
            dist[u] = INF_DIST;
        }
    }

    bool foundAugmenting = false;
    while (!q.empty()) {
        int u = q.front(); q.pop();
        for (int v : g[u]) {
            int matchedU = pairV[v];
            if (matchedU == -1) {
                foundAugmenting = true;
            } else if (dist[matchedU] == INF_DIST) {
                dist[matchedU] = dist[u] + 1;
                q.push(matchedU);
            }
        }
    }
    return foundAugmenting;
}

bool dfs(int u) {
    for (int v : g[u]) {
        int matchedU = pairV[v];
        if (matchedU == -1 || (dist[matchedU] == dist[u] + 1 && dfs(matchedU))) {
            pairU[u] = v;
            pairV[v] = u;
            return true;
        }
    }
    dist[u] = INF_DIST;
    return false;
}

void solve() {
    int n, m, k;
    cin >> n >> m >> k;

    g.assign(n, {});
    while (k--) {
        int u, v;
        cin >> u >> v;
        --u; --v;
        g[u].push_back(v);
    }

    pairU.assign(n, -1);
    pairV.assign(m, -1);
    dist.assign(n, INF_DIST);

    int matching = 0;
    while (bfs(n)) {
        for (int u = 0; u < n; ++u) {
            if (pairU[u] == -1 && dfs(u)) {
                ++matching;
            }
        }
    }

    cout << matching << endl;
}

int32_t main()
{
    // freopen("paint.in", "r", stdin);
    // freopen("paint.out", "w", stdout);
    fastIO;
    cout.precision(10);
    cout.setf(ios::fixed);
    int t = 1;
    for(int z = 1; z<=t; z++){
        // cout<<"Case "<<z<<": ";
        solve();
    }
}