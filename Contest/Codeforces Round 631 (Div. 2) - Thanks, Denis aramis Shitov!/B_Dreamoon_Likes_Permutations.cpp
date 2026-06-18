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
 mt19937 rng(chrono::steady_clock::now().time_since_epoch().count());
int getRandomNumber(int l, int r) {return uniform_int_distribution<int>(l, r)(rng);} 
 const int N = 2e5 + 10;
int Hash[N], pHash[N];
  void solve()
{
    int n;
    cin >> n;
    vector<int> arr(n + 1, 0);
    for(int i = 1; i <= n; i++){
     cin >> arr[i];
     arr[i] = Hash[arr[i]];
     arr[i] = (arr[i] ^ arr[i - 1]);
    }
    vector<pair<int,int>> ans;
    for(int i = 1; i <= n; i++){
     if(arr[i] == pHash[i] and (arr[n] ^ arr[i]) == pHash[n - i]){
      ans.push_back({i, n - i});
     }
    }
    cout << sz(ans) << endl;
    for(auto &[f, s]: ans){
     cout << f << " " << s << endl;
    }
}
 int32_t main()
{
    // freopen("paint.in", "r", stdin);
    // freopen("paint.out", "w", stdout);
    ios::sync_with_stdio(false), cin.tie(nullptr), cout.tie(nullptr);
    cout.precision(10);
    cout.setf(ios::fixed);
    for(int i = 1; i < N; i++){
     Hash[i] = getRandomNumber(1, 2e18);
    }
    pHash[0] = 0;
    for(int i = 1; i < N; i++){
     pHash[i] = (pHash[i - 1] ^ Hash[i]);
    }
    // for(int i = 1; i <= 10; i++){
    //  cerr << pHash[i] << " ";
    // }
    // cerr << endl;
    int t = 1;
    cin >> t;
    for (int z = 1; z <= t; z++)
    {
        // cout<<"Case "<<z<<": ";
        solve();
    }
}