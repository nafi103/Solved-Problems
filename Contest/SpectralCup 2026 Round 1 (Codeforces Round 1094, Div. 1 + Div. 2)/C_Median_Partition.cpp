#include <bits/stdc++.h>
 #include <ext/pb_ds/assoc_container.hpp>
#include <ext/pb_ds/tree_policy.hpp>
using namespace std;
  using namespace chrono;
using namespace __gnu_pbds;
 template <class T>
using pbds = tree<T, null_type, less<T>, rb_tree_tag, tree_order_statistics_node_update>;
 /****************************************************************/
 #define sz(x) (int)(x).size()
#define all(x) x.begin(), x.end()
#define endl "\n"
const int mod = 998244353;
const int inf = 1e4 + 10;
 #ifndef ONLINE_JUDGE
#include "debug.h"
#define debug(x) cerr << "Line " << __LINE__ << ": " << #x << " = "; _print(x); cerr << endl;
#else
#define debug(...)
#endif
 /****************************************************************/
const int N = 5000, dummy = -1e9;
int n, m;
int dp[N], arr[N];
bool median[N][N];
 void solve()
{
    cin >> n;
    set<int> s;
    for(int i = 0; i < n; i++){
        cin >> arr[i];
        s.insert(arr[i]);
    }
    map<int,int> compress;
    for(auto &x: s){
        compress[x] = sz(compress);
    }
    m = sz(compress);
    pbds<pair<int,int>> d;
    for(int i = 0; i < n; i++){
        arr[i] = compress[arr[i]];
        d.insert({arr[i], i});
    }
    int med = (*d.find_by_order(n / 2)).first;
    for(int i = 0; i < n; i++){
        for(int j = i; j < n; j++)
            median[i][j] = false;
    }
    for(int i = 0; i < n; i++){
        int cnt = 0, small = 0, big = 0;
        for(int j = i; j < n; j++){
            if(arr[j] < med)
                small++;
            else if(arr[j] > med)
                big++;
            else
                cnt++;
            int len = (j - i + 1);
            if((len + 1) / 2 > small and (len + 1) / 2 <= small + cnt)
                median[i][j] = true;
        }
    }
    for(int i = 0; i < n; i++){
        dp[i] = dummy;
    }
    for(int i = n - 1; i >= 0; i--){
        for(int j = i; j < n; j += 2){
            if(median[i][j])
                dp[i] = max(dp[i], 1 + (j + 1 == n ? 0: dp[j + 1]));
        }
    }
    cout << dp[0] << endl;
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