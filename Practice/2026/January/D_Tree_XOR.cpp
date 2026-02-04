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
vector<vector<int>> t(N);
int a[N], n, subtree_size[N], ans[N];

void input(){
    cin >> n;
    for(int i = 0; i < n; i++){
        cin >> a[i];
        subtree_size[i] = 1;
        t[i].clear();
    }
    int u, v;
    for(int i = 1; i < n; i++){
        cin >> u >> v;
        u--, v--;
        t[u].push_back(v);
        t[v].push_back(u);
    }
}

int f(int node, int par){
    int cost = 0;
    for(auto &child: t[node]){
        if(child != par){
            cost += f(child, node);
            subtree_size[node] += subtree_size[child];
        }
    }
    if(par != -1)
        cost += subtree_size[node] * (a[node] ^ a[par]);
    return cost;
}

void reroot(int node, int par){
    ans[node] = ans[par];
    ans[node] -= subtree_size[node] * (a[node] ^ a[par]);
    ans[node] += (n - subtree_size[node]) * (a[node] ^ a[par]);
    for(auto &child: t[node]){
        if(child != par)
            reroot(child, node);
    }
}

void solve()
{
    input();
    ans[0] = f(0, -1);
    for(auto &child: t[0]){
        reroot(child, 0);
    }
    for(int i = 0; i < n; i++){
        cout << ans[i] << (i == n - 1 ? '\n' : ' ');
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
    cin >> t;
    for (int z = 1; z <= t; z++)
    {
        // cout<<"Case "<<z<<": ";
        solve();
    }
}