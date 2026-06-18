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

int n, fd;
vector<set<int>> t;
vector<int> parent;

void input(){
    cin >> n;
    t.resize(n);
    parent.resize(n);
    for(int i = 1, u, v; i < n; i++){
        cin >> u >> v;
        u--, v--;
        t[u].insert(v);
        t[v].insert(u);
    }
}

void dfs(int node, int par, int d){
    parent[node] = par;
    if(node == n - 1)
        fd = d;
    for(auto &child: t[node]){
        if(child != par){
            dfs(child, node, d + 1);
        }
    }
}


void dfs_p(int node, int par, int &cnt){
    cnt++;
    for(auto &child: t[node]){
        if(child != par){
            dfs_p(child, node, cnt);
        }
    }
}

void solve()
{
    input();

    dfs(0, -1, 0);

    int v = n - 1, move_up = (fd - 1) / 2;
    while(move_up--){
        v = parent[v];
    }
    int u = parent[v];
    t[u].erase(v);
    t[v].erase(u);

    int cntF = 0;
    dfs_p(0, -1, cntF);

    if(2 * cntF > n){
        cout << "Fennec" << endl;
    }else{
        cout << "Snuke" << endl;
    }
}

int32_t main()
{
    // freopen("paint.in", "r", stdin);
    // freopen("paint.out", "w", stdout);
    ios::sync_with_stdio(false), cin.tie(nullptr), cout.tie(nullptr);
    cout.precision(10);
    cout.setf(ios::fixed);
    int t = 1;
    // cin >> t;
    for (int z = 1; z <= t; z++)
    {
        // cout<<"Case "<<z<<": ";
        solve();
    }
}