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
 void get_RBS_tree(vector<vector<int>> &t, string &s){
    int node_cnt = 0;
    stack<int> st;
    for(auto &x: s){
        if(x == '('){
            int u = node_cnt++;
            t.push_back(vector<int>());
            if(!st.empty()){
                int v = st.top();
                t[u].push_back(v);
                t[v].push_back(u);
            }
            st.push(u);
        }else{
            st.pop();
        }
    }
}
 void leaf_count(int node, int par, vector<vector<int>> &t, int &cnt){
    if(par != -1){
        if(sz(t[node]) == 1){
            cnt++;
            return;
        }
    }
    for(auto &child: t[node]){
        if(child != par)
            leaf_count(child, node, t, cnt);
    }
}
 int get_level(int node, int par, vector<vector<int>> &t, int l){
    int child_cnt = 0;
    for(auto &child: t[node]){
        if(child != par)
            child_cnt++;
    }
    if(child_cnt > 1)
        return l;
    for(auto &child: t[node]){
        if(child != par)
            return get_level(child, node, t, l + 1);
    }
    return 0;
}
 void solve()
{
    int n;
    cin >> n;
    string s, t;
    cin >> s >> t;
    s = "(" + s + ")";
    t = "(" + t + ")";
    vector<vector<int>> ts, tt;
    get_RBS_tree(ts, s);
    get_RBS_tree(tt, t);
    if(get_level(0, -1, ts, 0) != get_level(0, -1, tt, 0)){
        cout << "NO" << endl;
        return;
    }
    int ts_leaf = 0, tt_leaf = 0;
    leaf_count(0, -1, ts, ts_leaf);
    leaf_count(0, -1, tt, tt_leaf);
    if(ts_leaf != tt_leaf){
        cout << "NO" << endl;
        return;
    }
    cout << "YES" << endl;
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