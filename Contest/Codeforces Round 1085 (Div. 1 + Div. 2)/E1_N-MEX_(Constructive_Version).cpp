#include <bits/stdc++.h>
 using namespace std;
 /****************************************************************/
 #define int long long
#define sz(x) (int)(x).size()
#define all(x) x.begin(), x.end()
#define endl "\n"
const int mod = 998244353;
const int inf = 1e6;
 #ifndef ONLINE_JUDGE
#include "debug.h"
#define debug(x) cerr << "Line " << __LINE__ << ": " << #x << " = "; _print(x); cerr << endl;
#else
#define debug(...)
#endif
 /****************************************************************/
 void solve()
{
    int n;
    cin >> n;
    vector<int> arr(n);
    for(auto &x: arr)
        cin >> x;
    set<int> s;
    for(int i = 0; i < n; i++){
        s.insert(i);
        if(arr[i] < n - i - 1 or arr[i] > n){
            cout << "NO" << endl;
            return;
        }
        if(i and arr[i] > arr[i - 1]){
            cout << "NO" << endl;
            return;
        }
    }
    for(int i = 0; i < n; i++){
        s.erase(arr[i]);
    }
    cout << "YES" << endl;
    int last = n;
    for(int i = 0; i < n; i++){
        if(arr[i] < last)
            cout << inf << " \n"[i == n - 1];
        else{
            cout << *s.rbegin() << " \n"[i == n - 1];
            s.erase(*s.rbegin());
        }
        last = arr[i];
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