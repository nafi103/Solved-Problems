#include<bits/stdc++.h>
#define int long long
using namespace std;
#define all(x) x.begin(), x.end()
const int MAX = 5e6 + 6;
void solve()  {
    int n, p, s, a;
    cin >> n >> p >> s >> a;

    vector<int> m(n);
    for (int &i : m) {
        cin >>  i;
    }

    if (a == n or accumulate(all(m), 0ll) == p  + s) {
        cout << n << endl;
        return;
    }

    int ans = 0;
    priority_queue<int> pq;
    for (int i = 0, cnt = 0, sum = 0; i < n; i++) {
        sum += m[i];
        pq.push(m[i]);
        cnt++;
        while (a > 0 and sum > p + s and !pq.empty()) {
            sum -= pq.top();
            a -= 1;
            pq.pop();
        }
        if (sum <= p + s) {
            ans = cnt;
        }
    }
    cout << ans << endl;
}
int32_t main() {
    ios_base::sync_with_stdio(false);
    cin.tie(NULL);
    int tc;
    cin >> tc;

    for (int i = 1; i <= tc; i++) {
        // if (i - 1)  {
        //     cout << endl;
        // }
        // cout << "Case " << i << ": ";
        solve();
    }
    return 0;
}


