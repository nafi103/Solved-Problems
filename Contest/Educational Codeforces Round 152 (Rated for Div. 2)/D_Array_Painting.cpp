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
int n;
 int process(vector<int> &v){
    if(v.empty())
        return 0;
    int zeros = count(all(v), 0ll), one_block = 0;
    for(int i = 0; i < sz(v); i++){
        if(v[i] == 1 and (i == 0 or v[i - 1] == 0))
            one_block++;
    }
    return max(zeros, one_block);
}
 void solve()
{
    int ans = 0;
    cin >> n;
    vector<int> arr(n);
    for(int i = 0; i < n; i++){
        cin >> arr[i];
    }
    vector<bool>visited(n, false);
    for(int i = 0; i < n; i++){
        if(!visited[i] and arr[i] == 2){
            ans++;
            queue<int> q;
            q.push(i);
            visited[i] = true;
            while(!q.empty()){
                int f = q.front();
                q.pop();
                int left = f - 1, right = f + 1;
                if(left >= 0 and !visited[left]){
                    visited[left] = true;
                    if(arr[left] != 0)
                        q.push(left);
                }
                if(right < n and !visited[right]){
                    visited[right] = true;
                    if(arr[right] != 0)
                        q.push(right);
                }
            }
        }
    }
    vector<int> st;
    for(int i = 0; i < n; i++){
        if(visited[i]){
            ans += process(st);
            st.clear();
        }else{
            st.push_back(arr[i]);
        }
    }
    if(!st.empty())
        ans += process(st);
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
    for (int z = 1; z <= t; z++)
    {
        // cout<<"Case "<<z<<": ";
        solve();
    }
}