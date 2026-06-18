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
 void solve()
{
    int n, cnt = 0;
    cin >> n;
    string str;
    cin >> str;
    for(auto &c: str){
        if(c == '1')
            cnt++;
    }
    if(cnt == n){
        if(cnt & 1){
            cout << "NO" << endl;
        }else{
            cout << "YES" <<endl;
            for(int i = 2; i <= n; i++){
                cout << 1 << " " << i << endl;
            }
        }
        return;
    }
    if(cnt == 0 or (cnt & 1)){
        cout << "NO" << endl;
        return;
    }
    cout << "YES" << endl;
    str += str;
    int origin = 0;
    while(str[origin] != '1')
        origin++;
    int r = n + origin;
    vector<int> odd_nodes;
    vector<pair<int,int>> edges;
    for(int i = origin; i < r; i++){
        int node = i % n;
        if(str[node] == '0')
            edges.push_back({node, (i - 1) % n});
        if(str[i + 1] == '1')
            odd_nodes.push_back(node);
    }
    if(!odd_nodes.empty()){
        int root = odd_nodes.back();
        odd_nodes.pop_back();
        while(!odd_nodes.empty()){
            edges.push_back({root, odd_nodes.back()});
            odd_nodes.pop_back();
        }
    }
    for(auto &[u, v]: edges)
        cout << u + 1 << " " << v + 1 << endl;
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