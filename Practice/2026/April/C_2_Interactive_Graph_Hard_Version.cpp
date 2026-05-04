#include <bits/stdc++.h>

using namespace std;

/****************************************************************/

#define int long long
#define sz(x) (int)(x).size()
#define all(x) x.begin(), x.end()
const int mod = 998244353;
const int inf = 1e18 + 10;

#ifndef ONLINE_JUDGE
#include "debug.h"
#define debug(x) cerr << "Line " << __LINE__ << ": " << #x << " = "; _print(x); cerr << endl;
#else
#define debug(...)
#endif

/****************************************************************/

vector<vector<int>> g;

vector<int> query(int i){
    cout << "? " << i << endl;
    int q;
    cin >> q;
    if(q == 0)
        return {};
    vector<int> path(q);
    for(int i = 0; i < q; i++)
        cin >> path[i];
    return path;
}

void calc(int node, vector<int> &path_cnt){
    if(path_cnt[node] != -1)
        return;
    path_cnt[node] = 1;
    for(auto &adj: g[node]){
        calc(adj, path_cnt);
        path_cnt[node] += path_cnt[adj];
    }
}

void solve()
{
    g.clear();
    int n;
    cin >> n;
    g.resize(n + 1);
    vector<int> path_cnt(n + 1, -1), prev_path = {1};
    int cnt = 2;
    vector<pair<int,int>> edges;
    while(true){
        vector<int> path = query(cnt);
        int m = sz(path);
        if(m == 0)
            break;
        if(m > 1){
            g[path[m - 2]].push_back(path[m - 1]);
            edges.push_back({path[m - 2], path[m - 1]});
        }
        int p = 0;
        for(int i = 0; i < min(sz(prev_path), m); i++, p++){
            if(path[i] != prev_path[i])
                break;
        }
        if(sz(prev_path) > p){
            calc(prev_path[p], path_cnt);
        }
        if(path_cnt[path[p]] == -1)
            cnt++;
        else
            cnt += path_cnt[path[p]];
        prev_path = path;
    }
    cout << "! " << sz(edges) << endl;
    for(auto &[u, v]: edges)
        cout << u << " " << v << endl;
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