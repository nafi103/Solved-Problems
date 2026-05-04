#include <bits/stdc++.h>
#pragma GCC optimize("Ofast,unroll-loops")
using namespace std;

/****************************************************************/

#define int unsigned long long
#define sz(x) (int)(x).size()
#define all(x) x.begin(), x.end()
#define endl "\n"
const int mod = 998244353;
const int inf = LLONG_MAX;

// #ifndef ONLINE_JUDGE
// #include "debug.h"
// #define debug(x) cerr << "Line " << __LINE__ << ": " << #x << " = "; _print(x); cerr << endl;
// #else
// #define debug(...)
// #endif

/****************************************************************/

mt19937 rng(chrono::steady_clock::now().time_since_epoch().count());
int getRandomNumber(int l, int r) {return uniform_int_distribution<int>(l, r)(rng);} 

const int N = 1e5 + 5;
int ans[N], arr[N], root, n;
vector<vector<int>> t(N);
vector<set<int>> sack(N);
vector<set<int>> list_sack(N);
vector<int> node_list(N);

void input(){
    cin >> n;
    map<int,int> compressed;
    for(int i = 1; i <= n; i++){
        cin >> arr[i];
        if(compressed.count(arr[i]) == 0){
            compressed[arr[i]] = getRandomNumber(1, inf);
        }
        arr[i] = compressed[arr[i]];
        t[i].clear();
        sack[i].clear();
        list_sack[i].clear();
        node_list[i] = 0;
    }
    for(int u = 1, p; u <= n; u++){
        cin >> p;
        if(p == -1){
            root = u;
        }else{
            t[u].push_back(p);
            t[p].push_back(u);
        }
    }
}

void dfs(int node, int par){
    int big_child = -1, mx = 1;
    for(auto &child: t[node]){
        if(child != par){
            dfs(child, node);
            if(sz(sack[child]) > mx){
                big_child = child;
                mx = sz(sack[child]);
            }
        }
    }
    if(big_child != -1){
        swap(sack[node], sack[big_child]);
        swap(node_list[node], node_list[big_child]);
        swap(list_sack[node], list_sack[big_child]);
    }
    for(auto &child: t[node]){
        if(child != par and child != big_child){
            for(auto &x: sack[child]){
                if(sack[node].count(x) == 0){
                    node_list[node] ^= x;
                    sack[node].insert(x);
                }
            }
            for(auto &h: list_sack[child])
                list_sack[node].insert(h);
        }
    }
    if(sack[node].count(arr[node]) == 0){
        node_list[node] ^= arr[node];
        sack[node].insert(arr[node]);
    }
    list_sack[node].insert(node_list[node]);
    ans[node] = sz(list_sack[node]);
}

void solve()
{
    input();
    dfs(root, -1);
    for(int i = 1; i <= n; i++){
        cout << ans[i] << " \n"[i == n];
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