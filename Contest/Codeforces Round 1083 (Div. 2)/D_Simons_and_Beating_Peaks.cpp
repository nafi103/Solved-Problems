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
 vector<int> f(vector<int> &arr, int n){
    vector<int> ans(n);
    ans[n - 1] = 0;
    stack<int> st;
    st.push(arr[n - 1]);
    for(int i = n - 2; i >= 0; i--){
        while(!st.empty() and st.top() <= arr[i])
            st.pop();
        ans[i] = sz(st);
        st.push(arr[i]);
    }
    return ans;
}
 void solve()
{
    int n;
    cin >> n;
    vector<int> arr(n);
    for(int i = 0; i < n; i++){
        cin >> arr[i];
    }
    vector<int> right = f(arr, n);
    reverse(all(arr));
    vector<int> left = f(arr, n);
    reverse(all(left));
    int ans = n;
    for(int i = 0; i < n; i++){
        ans = min(ans , n - (left[i] + right[i] + 1));
    }
    cout << ans << endl;
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