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

const int m = (1ll << 31) - 1, N = 1e5 + 10;
vector<vector<pair<int,int>>>g;
int n, q, can_be[N], cannot_be[N], value[N];

void input(){
    cin >> n >> q;
    g.resize(n + 1);
    for(int i = 0; i < q; i++){
        int u, v, x;
        cin >> u >> v >> x;
        if(u == v){
            value[u] = x;
            cannot_be[u] = (cannot_be[u] | (m ^ x));
            continue;
        }
        g[u].emplace_back(v, x);
        g[v].emplace_back(u, x);
        cannot_be[u] = (cannot_be[u] | (m ^ x));
        cannot_be[v] = (cannot_be[v] | (m ^ x));
    }
    for(int i = 1; i <= n; i++){
        sort(all(g[i]));
        can_be[i] = m - cannot_be[i];
    }
}

void solve()
{
    input();
    for(int i = 1; i <= n; i++){
        for(int j = 29; j >= 0; j--){
            if(value[i] & (1 << j))
                continue;
            int add = 0;
            for(auto &[adj, x]: g[i]){
                if((x & (1 << j)) and (cannot_be[adj] & (1 << j))){
                    add = 1 << j;
                }
            }
            if(add)
                value[i] += add;
            else{
                for(auto &[adj, x]: g[i]){
                    if(x & (1 << j)){
                        value[adj] |= (1 << j);
                    }
                }
            }
        }
    }
    for(int i = 1; i <= n; i++)
        cout << value[i] << (i == n ? '\n' : ' ');
}

int32_t main()
{
    // freopen("paint.in", "r", stdin);
    // freopen("paint.out", "w", stdout);
    ios::sync_with_stdio(false), cin.tie(nullptr), cout.tie(nullptr);
    cout.precision(10);
    cout.setf(ios::fixed);
    int t = 1;
    for (int z = 1; z <= t; z++)
    {
        // cout<<"Case "<<z<<": ";
        solve();
    }
}