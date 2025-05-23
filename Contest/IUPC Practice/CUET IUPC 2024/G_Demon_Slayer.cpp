#include <bits/stdc++.h>
#define int long long
using namespace std;

const int MAX = 5e6 + 6;
const pair<int, int> VERTICAL = {1, 0};
const pair<int, int> HORIZONTAL = {0, 1};

pair<int, int> calc_slope(int dy, int dx) {
    if (dy == 0) return HORIZONTAL;
    if (dx == 0) return VERTICAL;
    int g = gcd(abs(dy), abs(dx));
    dy /= g;
    dx /= g;
    if (dx < 0) {
        dy *= -1;
        dx *= -1;
    }
    return {dy, dx};
}

int32_t main() {
    ios_base::sync_with_stdio(false);
    cin.tie(NULL);

    int n, m;
    cin >> n >> m;

    vector<pair<int, int>> demon(m);
    for (auto &[x, y] : demon) {
        cin >> x >> y;
    }

    vector<int> ans(n + 1, 1);

    for (int i = 0; i < m; i++) {
        int same_point = 0;
        map<pair<int, int>, int> slope_count;

        for (int j = 0; j < m; j++) {
            if (i == j) continue;
            if (demon[i] == demon[j]) {
                same_point++;
                continue;
            }

            auto slope = calc_slope(demon[j].second - demon[i].second,
                                    demon[j].first - demon[i].first);
            slope_count[slope]++;
        }

        for (auto &[slope, cnt] : slope_count) {
            if (slope == HORIZONTAL || slope == VERTICAL) {
                if (slope == VERTICAL && demon[i].first >= 1 && demon[i].first <= n)
                    ans[demon[i].first] = max(ans[demon[i].first], cnt + 1);
                continue;
            }

            int dy = slope.first;
            int dx = slope.second;
            int y = demon[i].second;
            int x = demon[i].first;

            if (dy != 0 && y % dy == 0) {
                int steps = y / dy;
                int laser_x = x - steps * dx;
                if (laser_x >= 1 && laser_x <= n) {
                    ans[laser_x] = max(ans[laser_x], cnt + same_point + 1);
                }
            }
        }
    }

    for (int i = 1; i <= n; i++) {
        cout << ans[i] << " ";
    }
    cout << "\n";

    return 0;
}
