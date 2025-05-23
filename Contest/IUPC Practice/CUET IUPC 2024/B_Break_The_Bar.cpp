#include<bits/stdc++.h>
#define int long long
using namespace std;
#define all(x) x.begin(), x.end()
const int MAX = 5e6 + 6;
void solve()  {
    int n, m, p;
    cin >> n >> m >> p;

    if  (m * n < p) {
        cout <<  -1 << endl;
        return;
    }

    if (n * m == p) {
        cout <<  p - 1 <<  endl;
    } else if (p % n == 0 or p %  m == 0){
        cout << n << endl;
    } else if (p >= m and p >= n) {
        bool possible = false;
        for (int i = 0; i <= min(m, n); i++){
            int tot_by_row = n * i;
            int rem = p - tot_by_row;
            int cur_col = m - i;

            if (rem % cur_col ==0){
                possible = true;
            }

            int tot_by_col = m * i;
            rem = p - tot_by_col;
            int cur_row = n - i;
            if (rem % cur_row == 0) {
                possible = true;
            }
            if  (possible) break;
        }
        cout << p + !possible << endl;
    } else {
        cout << p + 1 << endl;
    }

}
int32_t main() {
    ios_base::sync_with_stdio(false);
    cin.tie(NULL), cout.tie(NULL);
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