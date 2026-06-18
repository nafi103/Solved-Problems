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
 /*
Every non prime is reachable by 2
Only the primes in the given array matters
 Base case: There can't be two prime in the array
 Two case after sorting:
1. First element is prime. Must take that prime. That prime should generate all other.
2. First element is not prime. In that case 2 should generate all other numbers
 */
 const int N = 4e5 + 10;
int spf[N], arr[100000];
vector<int> pr;
 void solve()
{
    int n, cnt = 0;
    cin >> n;
     for(int i = 0; i < n; i++){
        cin >> arr[i];
        if(spf[arr[i]] == arr[i])
            cnt++;
    }
     if(n == 1){
        cout << arr[0] << endl;
        return;
    }
     if(cnt > 1){
        cout << -1 << endl;
        return;
    }
     if(cnt == 0){
        cout << 2 << endl;
        return;
    }
     sort(arr, arr + n);
     if(spf[arr[0]] != arr[0]){
        cout << -1 << endl;
        return;
    }
     int even = -1, odd = -1;
    for(int i = 1; i < n; i++){
        if((arr[i] & 1) == 0){
            even = arr[i];
            break;
        }
    }
    for(int i = 1; i < n; i++){
        if(arr[i] & 1){
            odd = arr[i];
            break;
        }
    }
     if(even != -1){
        if(even < 2 * arr[0]){
            cout << -1 << endl;
            return;
        }
    }
     if(odd != -1){
        odd -= spf[odd];
        if(odd < 2 * arr[0]){
            cout << -1 << endl;
            return;
        }
    }
     cout << arr[0] << endl;
}
 int32_t main()
{
    // freopen("paint.in", "r", stdin);
    // freopen("paint.out", "w", stdout);
    ios::sync_with_stdio(false), cin.tie(nullptr), cout.tie(nullptr);
    cout.precision(10);
    cout.setf(ios::fixed);
     for (int i = 2; i < N; ++i) {
        if (spf[i] == 0) {
            spf[i] = i;
            pr.push_back(i);
        }
        for (int j = 0; i * pr[j] < N; ++j) {
            spf[i * pr[j]] = pr[j];
            if (pr[j] == spf[i]) {
                break;
            }
        }
    }
     int t = 1;
    cin >> t;
    for (int z = 1; z <= t; z++)
    {
        // cout<<"Case "<<z<<": ";
        solve();
    }
}