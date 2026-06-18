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
int pxor[N];
 void solve()
{
    int n, k, x;
    cin >> n >> k >> x;
    if(k & 1){
        if(pxor[n] != x){
            cout << "NO" << endl;
            return;
        }
    }else{
        if(pxor[n] != 0){
            cout << "NO" << endl;
            return;
        }
    }
     int msb = 63 - __builtin_clzll(x), msb_val = (1 << msb), p = 0;
    vector<bool> visited(n + 1, false);
    vector<vector<int>> arr(k);
    for(int i = 0; p < k and i <= n; i++){
        int j = i | msb_val;
        if(j <= n and !visited[j]){
            visited[j] = true;
            arr[p].push_back(j);
            p++;
        }
    }
     if(p < k){
        cout << "NO" << endl;
        return;
    }
     cout << "YES" << endl;
    for(int i = 0; i < k; i++){
        if(arr[i].back() != x){
            arr[i].push_back(arr[i].back() ^ x);
            visited[arr[i].back()] = true;
        }
    }
    for(int i = 1; i <= n; i++){
        if(!visited[i])
            arr[0].push_back(i);
    }
     for(auto &v: arr){
        cout << sz(v);
        for(auto &x: v){
            cout << " " << x;
        }
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
     pxor[0] = 0;
    for(int i = 1; i < N; i++){
        pxor[i] = (pxor[i - 1] ^ i);
    }
     int t = 1;
    cin >> t;
    for (int z = 1; z <= t; z++)
    {
        // cout<<"Case "<<z<<": ";
        solve();
    }
}