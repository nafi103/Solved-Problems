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
int level[N], cnt[N], parent[N];

void dfs(int node, int par, int l){
    level[node] = l;
    parent[node] = par;
    for(auto &child: t[node]){
        if(child != par){
            dfs(child, node, l + 1);
        }
    }
}

void solve()
{
    int n;
    cin >> n;
    for(int i = 0; i < n; i++){
        t[i].clear();
        cnt[i] = 0;
    }
    for(int i = 1, u, v; i < n; i++){
        cin >> u >> v;
        u--, v--;
        t[u].push_back(v);
        t[v].push_back(u);
    }

    dfs(0, -1, 0);

    int mn = sz(t[0]) + 1;
    for(int i = 0; i < n; i++){
        mn = max(mn, sz(t[i]));
    }
    for(int i = 0; i < n; i++){
        cnt[level[i]]++;
    }

    int ans_sz = max(*max_element(cnt, cnt + n), mn);

    vector<int> color(n, - 1);
    color[0] = 0;
    vector<vector<int>> ans(ans_sz);

    map<int, vector<int>>  same_level;
    for(int i = 1; i < n; i++){
        same_level[level[i]].push_back(i);
    }

    for(auto &[l, arr]: same_level){
        sort(all(arr), [&](int &a, int &b){
            return parent[a] < parent[b];
        });

        vector<int> available(min(ans_sz, sz(arr) + 1));
        iota(all(available), 0ll);

        for(auto &node: arr){
            int par = parent[node];
            if(color[par] != available.back()){
                color[node] = available.back();
                available.pop_back();
            }else{
                if(sz(available) >= 2){
                    swap(available[sz(available) - 1], available[sz(available) - 2]);
                    color[node] = available.back();
                    available.pop_back();
                }else{
                    color[node] = available[0];
                    available.pop_back();
                    swap(color[node], color[arr[0]]);
                }
            }
        }
    }

    for(int i = 0; i < n; i++){
        ans[color[i]].push_back(i);
    }

    cout << sz(ans) << endl;
    for(auto &arr: ans){
        cout << sz(arr);
        for(auto &x: arr)
            cout << " " << x + 1;
        cout << endl;
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