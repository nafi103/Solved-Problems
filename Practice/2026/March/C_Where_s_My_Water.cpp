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

const int N = 2005;
int n, h;
vector<int> left_drain(N), right_drain(N), arr(N), tmp(N);

void input(){
    cin >> n >> h;
    for(int i = 0; i < n; i++)
        cin >> arr[i];
}

void solve()
{
    input();
    int ans = 0;
    for(int i = 0; i < n; i++){
        int mx = arr[i], flush = 0;
        for(int j = i; j < n; j++){
            mx = max(mx, arr[j]);
            flush += h - mx;
            tmp[j] = mx - arr[j];
        }
        mx = arr[i];
        for(int j = i - 1; j >= 0; j--){
            mx = max(mx, arr[j]);
            flush += h - mx;
            tmp[j] = mx - arr[j];
        }
        fill(left_drain.begin(), left_drain.begin() + n, 0ll);
        stack<int> st;
        for(int j = 0; j < n; j++){
            while(!st.empty() and tmp[st.top()] >= tmp[j])
                st.pop();
            if(st.empty()){
                left_drain[j] += tmp[j] * (j + 1);
            }else{
                left_drain[j] += (tmp[j] * (j - st.top())) + left_drain[st.top()];
            }
            st.push(j);
        }
        while(!st.empty())
            st.pop();
        fill(right_drain.begin(), right_drain.begin() + n, 0ll);
        for(int j = n - 1; j >= 0; j--){
            while(!st.empty() and tmp[st.top()] >= tmp[j])
                st.pop();
            if(st.empty()){
                right_drain[j] += tmp[j] * (n - 1 - j);
            }else{
                right_drain[j] += (tmp[j] * (st.top() - j - 1)) + tmp[st.top()] + right_drain[st.top()];
            }
            st.push(j);
        }
        mx = 0;
        for(int j = 0; j < n; j++)
            mx = max(left_drain[j] + right_drain[j], mx);
        ans = max(ans, mx + flush);
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