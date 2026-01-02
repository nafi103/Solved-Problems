#include <bits/stdc++.h>

using namespace std;

/****************************************************************/

#define int long long
#define sz(x) (int)(x).size()
#define all(x) x.begin(), x.end()
#define endl "\n"
const int mod = 1e9 + 7;
const int inf = 1e18 + 10;

#ifndef ONLINE_JUDGE
#include "debug.h"
#define debug(x) cerr << "Line " << __LINE__ << ": " << #x << " = "; _print(x); cerr << endl;
#else
#define debug(...)
#endif

/****************************************************************/

const int N = 2e5 + 2;
vector<vector<int>> t(N), subtree_level(N);
int n, sum[N], power_of_two[N], ans;

void input(){
    cin >> n;
    subtree_level[0].clear();
    for(int i = 0; i < n; i++){
        sum[i] = 0;
        t[i].clear();
    }
    int u,v;
    for(int i = 1; i < n; i++){
        cin >> u >> v;
        u--,v--;
        t[u].push_back(v);
        t[v].push_back(u);
    }
    ans = (n * power_of_two[n - 1]) % mod;
}

void dfs(int node, int parent){
    int big_child = -1, mx_len = -1;
    for(auto &child: t[node]){
        if(child != parent){
            dfs(child, node);
            if(sz(subtree_level[child]) > mx_len){
                mx_len = sz(subtree_level[child]);
                big_child = child;
            }
        }
    }
    if(big_child != -1){
        swap(sum[node], sum[big_child]);
        swap(subtree_level[node], subtree_level[big_child]);
    }
    vector<int> &a = subtree_level[node];
    for(auto &child: t[node]){
        if(child != parent and child != big_child){
            vector<int> &b = subtree_level[child];
            for(int i = 0, j = sz(a) - sz(b); i < sz(b); i++, j++){
                sum[node] = (sum[node] - (power_of_two[a[j] - 1] * power_of_two[n - a[j]]) % mod + mod) % mod;
                a[j] += b[i];
                sum[node] = (sum[node] + (power_of_two[a[j] - 1] * power_of_two[n - a[j]]) % mod) % mod;
            }
            b.clear();
        }
    }
    ans = (ans + sum[node]) % mod;
    sum[node] = (sum[node] + power_of_two[n - 1]) % mod;
    a.push_back(1);
}

void solve()
{
    input();
    dfs(0, - 1);
    cout << ans << endl;
}

int32_t main()
{
    // freopen("paint.in", "r", stdin);
    // freopen("paint.out", "w", stdout);
    ios::sync_with_stdio(false), cin.tie(nullptr), cout.tie(nullptr);
    cout.precision(10);
    cout.setf(ios::fixed);
    power_of_two[0] = 1;
    for(int i = 1; i < N; i++){
        power_of_two[i] = (power_of_two[i - 1] * 2) % mod;
    }
    int t = 1;
    cin >> t;
    for (int z = 1; z <= t; z++)
    {
        // cout<<"Case "<<z<<": ";
        solve();
    }
}