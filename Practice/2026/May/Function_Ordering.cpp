#include <bits/stdc++.h>

using namespace std;

/****************************************************************/

#define int long long
#define sz(x) (int)(x).size()
#define all(x) x.begin(), x.end()
#define endl "\n"
const int mod = 998244353;
const int inf = 1e18 + 10;

#ifndef ONLINE_JUDGE
#include "debug.h"
#define debug(x) cerr << "Line " << __LINE__ << ": " << #x << " = "; _print(x); cerr << endl;
#else
#define debug(...)
#endif

/****************************************************************/

const int N = 2e5 + 10;
vector<int> t[N];
int a[N], b[N];

void dfs(int node, int par){
    for(auto &child: t[node]){
        if(child != par)
            dfs(child, node);
    }

    vector<pair<int,int>> arr;
    for(auto &child: t[node]){
        if(child != par)
            arr.push_back({a[child], b[child]});
    }

    sort(all(arr), [&](pair<int,int> &l, pair<int,int> &r){
        return l.second * (r.first - 1) < r.second * (l.first - 1);
    });

    while(!arr.empty()){
        auto [ca, cb] = arr.back();
        arr.pop_back();
        int fa = (a[node] * ca);
        int fb = (ca * b[node] + cb);
        a[node] = fa;
        b[node] = fb;
    }
}

void solve()
{
    int n;
    cin >> n;
    vector<array<int, 3>> p(n);
    for (int i = 0; i < n; i++)
    {
        t[i].clear();
        cin >> a[i] >> b[i];
    }

    for (int i = 1, u, v; i < n; i++)
    {
        cin >> u >> v;
        u--, v--;
        t[u].push_back(v);
        t[v].push_back(u);
    }

    dfs(0, -1);
    cout << b[0] << endl;
}

int32_t main()
{
    // freopen("paint.in", "r", stdin);
    // freopen("paint.out", "w", stdout);
    ios::sync_with_stdio(false), cin.tie(nullptr), cout.tie(nullptr);
    cout.precision(10);
    cout.setf(ios::fixed);
    int t = 1;
    cin >> t;
    for (int z = 1; z <= t; z++)
    {
        // cout<<"Case "<<z<<": ";
        solve();
    }
}